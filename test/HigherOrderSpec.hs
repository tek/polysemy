module HigherOrderSpec where

import Polysemy.Internal.Tactics (interpretBindHO)
import Polysemy.Internal.Tactics (interpretHO)
import Polysemy.Internal (send)
import Polysemy
import Polysemy.Reader
import Test.Hspec

data TestE :: Effect where
  TestE :: m a -> (a -> m b) -> TestE m b

interpretTestE :: InterpreterFor TestE r
interpretTestE =
  interpretH $ \case
    TestE ma f -> do
      a <- interpretHO ma
      interpretBindHO f a

spec :: Spec
spec = parallel $ describe "Reader local" $ do
  it "should nest with itself" $ do
    let foo = run . runReader "hello" $ do
                local (++ " world") $ do
                  local (++ "!") $ do
                    ask
    foo `shouldBe` "hello world!"
  it "interpretHO" $ do
    r <- runM (interpretTestE (send (TestE (pure 5) (pure . (9 +)))))
    print r
    (14 :: Int) `shouldBe` r
