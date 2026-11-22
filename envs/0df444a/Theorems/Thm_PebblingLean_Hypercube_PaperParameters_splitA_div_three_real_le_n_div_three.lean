-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitA_div_three_real_le_n_div_three
-- name    : PebblingLean.Hypercube.PaperParameters.splitA_div_three_real_le_n_div_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:58:28.339796+00:00
-- url     : https://prove2.me/theorems/797f92b8-97de-4a66-8700-8a7154488a56
-- title:
--   Paper Parameters: split A div three real le n div three
-- statement:
--   The Paper Parameters construction uses the split A div three real le n div three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L506-L512
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L506-L512

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

theorem PebblingLean.Hypercube.PaperParameters.splitA_div_three_real_le_n_div_three {K : ℝ} {n : ℕ} :
    ((splitA K n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := by sorry
