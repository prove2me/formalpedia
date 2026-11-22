-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_core_le_real
-- name    : PebblingLean.Hypercube.PaperParameters.splitM_core_le_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:58:12.550891+00:00
-- url     : https://prove2.me/theorems/e87b2989-3d25-4c3c-ad1b-1e5e23c8f75a
-- title:
--   Paper Parameters: split M core le real
-- statement:
--   The Paper Parameters construction uses the split M core le real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L428-L431
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L428-L431

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

theorem PebblingLean.Hypercube.PaperParameters.splitM_core_le_real {K : ℝ} {n : ℕ} :
    K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (splitM K n : ℝ) := by sorry
