-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitA_div_three_le_rOut
-- name    : PebblingLean.Hypercube.PaperParameters.splitA_div_three_le_rOut
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:45.267503+00:00
-- url     : https://prove2.me/theorems/9ef6ceec-e250-4450-b5c7-5c8a3f456ef0
-- title:
--   Paper Parameters: split A div three le r Out
-- statement:
--   The Paper Parameters construction uses the split A div three le r Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L104-L107
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L104-L107

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

theorem PebblingLean.Hypercube.PaperParameters.splitA_div_three_le_rOut {A K : ℝ} {n : ℕ} :
    splitA K n / 3 ≤ rOut A K n := by sorry
