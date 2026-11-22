-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicitCutoff_splitThreshold
-- name    : PebblingLean.Hypercube.PaperParameters.explicitCutoff_splitThreshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:30.339078+00:00
-- url     : https://prove2.me/theorems/c7974727-f01a-402e-9bfa-6af1b54a0637
-- title:
--   Paper Parameters: explicit Cutoff split Threshold
-- statement:
--   The Paper Parameters construction uses the explicit Cutoff split Threshold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5744-L5746
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L5744-L5746

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

theorem PebblingLean.Hypercube.PaperParameters.explicitCutoff_splitThreshold :
    (128 * (217 : ℝ) ^ 2) ^ 2 ≤ (explicitCutoff : ℝ) := by sorry
