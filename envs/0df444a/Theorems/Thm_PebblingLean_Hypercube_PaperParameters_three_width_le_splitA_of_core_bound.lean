-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_three_width_le_splitA_of_core_bound
-- name    : PebblingLean.Hypercube.PaperParameters.three_width_le_splitA_of_core_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:57.283666+00:00
-- url     : https://prove2.me/theorems/9581b991-cab0-4955-89ee-e16ffea42da3
-- title:
--   Paper Parameters: three width le split A of core bound
-- statement:
--   The Paper Parameters construction uses the three width le split A of core bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L157-L174
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L157-L174

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

theorem PebblingLean.Hypercube.PaperParameters.three_width_le_splitA_of_core_bound {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A)
    (hcore :
      3 * (annulusWidthCore A K n + 1) ≤ (splitA K n : ℝ)) :
    3 * annulusWidth A K n ≤ splitA K n := by sorry
