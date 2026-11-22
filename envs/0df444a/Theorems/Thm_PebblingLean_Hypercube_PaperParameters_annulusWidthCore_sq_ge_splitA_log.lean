-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulusWidthCore_sq_ge_splitA_log
-- name    : PebblingLean.Hypercube.PaperParameters.annulusWidthCore_sq_ge_splitA_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:37.4702+00:00
-- url     : https://prove2.me/theorems/e86b61c5-f484-4600-bcf8-7d9753532739
-- title:
--   Paper Parameters: annulus Width Core sq ge split A log
-- statement:
--   The real annulus-width core has square at least
--   `A^2 a log n`, where `a=splitA K n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L583-L595
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L583-L595

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

theorem PebblingLean.Hypercube.PaperParameters.annulusWidthCore_sq_ge_splitA_log {A K : ℝ} {n : ℕ}
    (hn : 1 ≤ n) :
    A ^ 2 * ((splitA K n : ℝ) * Real.log (n : ℝ)) ≤
      (annulusWidthCore A K n) ^ 2 := by sorry
