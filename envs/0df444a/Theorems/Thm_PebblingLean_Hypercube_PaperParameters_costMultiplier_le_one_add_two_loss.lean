-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_costMultiplier_le_one_add_two_loss
-- name    : PebblingLean.Hypercube.PaperParameters.costMultiplier_le_one_add_two_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:17.826073+00:00
-- url     : https://prove2.me/theorems/d41a1b04-2970-435e-9d0e-97f08cb8ebbb
-- title:
--   Paper Parameters: cost Multiplier le one add two loss
-- statement:
--   The integer fiber multiplier is bounded by a `1+2 n^{-2}` real multiplier
--   once the additive ceiling error is absorbed by the extra `n^{-2}` slack.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1978-L1995
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1978-L1995

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters

theorem PebblingLean.Hypercube.PaperParameters.costMultiplier_le_one_add_two_loss {K : ℝ} {n : ℕ}
    (hslack : 1 ≤ loss n * (((4 : ℝ) / 3) ^ splitA K n)) :
    (costMultiplier K n : ℝ) ≤
      (1 + 2 * loss n) * (((4 : ℝ) / 3) ^ splitA K n) := by sorry
