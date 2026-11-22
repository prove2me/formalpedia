-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_rIn_le_rOut
-- name    : PebblingLean.Hypercube.PaperParameters.rIn_le_rOut
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:48.084669+00:00
-- url     : https://prove2.me/theorems/fe8d8e54-badd-4676-9e88-8eae8ea3f36d
-- title:
--   Paper Parameters: r In le r Out
-- statement:
--   The Paper Parameters construction uses the r In le r Out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L99-L102
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L99-L102

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

theorem PebblingLean.Hypercube.PaperParameters.rIn_le_rOut {A K : ℝ} {n : ℕ} :
    rIn A K n ≤ rOut A K n := by sorry
