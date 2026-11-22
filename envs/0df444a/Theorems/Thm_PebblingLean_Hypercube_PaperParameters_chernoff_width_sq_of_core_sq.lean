-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_chernoff_width_sq_of_core_sq
-- name    : PebblingLean.Hypercube.PaperParameters.chernoff_width_sq_of_core_sq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:56.811972+00:00
-- url     : https://prove2.me/theorems/c779e87c-3ecf-423a-9087-9f194be24b74
-- title:
--   Paper Parameters: chernoff width sq of core sq
-- statement:
--   The Paper Parameters construction uses the chernoff width sq of core sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L147-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L147-L155

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

theorem PebblingLean.Hypercube.PaperParameters.chernoff_width_sq_of_core_sq {A K : ℝ} {n : ℕ}
    (hA : 0 ≤ A)
    (hcoreSq :
      12 * ((splitA K n : ℝ) + 1) * Real.log (n : ℝ) ≤
        (annulusWidthCore A K n) ^ 2) :
    12 * ((splitA K n : ℝ) + 1) * Real.log (n : ℝ) ≤
      (annulusWidth A K n : ℝ) ^ 2 := by sorry
