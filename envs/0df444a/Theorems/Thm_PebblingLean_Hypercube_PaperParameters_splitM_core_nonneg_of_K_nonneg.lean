-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_core_nonneg_of_K_nonneg
-- name    : PebblingLean.Hypercube.PaperParameters.splitM_core_nonneg_of_K_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:55:59.08404+00:00
-- url     : https://prove2.me/theorems/e3c7a200-deaf-4596-b396-127f00a5c990
-- title:
--   Paper Parameters: split M core nonneg of K nonneg
-- statement:
--   The Paper Parameters construction uses the split M core nonneg of K nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L381-L384
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L381-L384

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

theorem PebblingLean.Hypercube.PaperParameters.splitM_core_nonneg_of_K_nonneg {K : ℝ} {n : ℕ}
    (hK : 0 ≤ K) :
    0 ≤ K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by sorry
