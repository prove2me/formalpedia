-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusChernoffLambda_nonneg
-- name    : PebblingLean.Hypercube.PaperParameters.annulusChernoffLambda_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:18.480803+00:00
-- url     : https://prove2.me/theorems/61016ba7-cd5b-463a-8db4-417f7eacf1b1
-- title:
--   Paper Parameters: annulus Chernoff Lambda nonneg
-- statement:
--   The Paper Parameters construction uses the annulus Chernoff Lambda nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3537-L3540
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3537-L3540

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

theorem PebblingLean.Hypercube.PaperParameters.annulusChernoffLambda_nonneg (A K : ℝ) (n : ℕ) :
    0 ≤ annulusChernoffLambda A K n := by sorry
