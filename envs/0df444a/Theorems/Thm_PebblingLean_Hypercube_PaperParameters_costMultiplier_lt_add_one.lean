-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_costMultiplier_lt_add_one
-- name    : PebblingLean.Hypercube.PaperParameters.costMultiplier_lt_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:08:52.380202+00:00
-- url     : https://prove2.me/theorems/efc12630-5bd1-4298-b54f-5cad47c3ae6e
-- title:
--   Paper Parameters: cost Multiplier lt add one
-- statement:
--   The Paper Parameters construction uses the cost Multiplier lt add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L701-L705
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L701-L705

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

theorem PebblingLean.Hypercube.PaperParameters.costMultiplier_lt_add_one {K : ℝ} {n : ℕ}
    (hnonneg : 0 ≤ (1 + loss n) * (((4 : ℝ) / 3) ^ splitA K n)) :
    (costMultiplier K n : ℝ) <
      (1 + loss n) * (((4 : ℝ) / 3) ^ splitA K n) + 1 := by sorry
