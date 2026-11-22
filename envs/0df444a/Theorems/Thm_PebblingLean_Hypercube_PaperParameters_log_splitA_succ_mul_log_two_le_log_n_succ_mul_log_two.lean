-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_log_splitA_succ_mul_log_two_le_log_n_succ_mul_log_two
-- name    : PebblingLean.Hypercube.PaperParameters.log_splitA_succ_mul_log_two_le_log_n_succ_mul_log_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:59:48.312161+00:00
-- url     : https://prove2.me/theorems/043921d6-9db3-464d-b390-1ba829408900
-- title:
--   Paper Parameters: log split A succ mul log two le log n succ mul log two
-- statement:
--   The Paper Parameters construction uses the log split A succ mul log two le log n succ mul log two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1059-L1071
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1059-L1071

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

theorem PebblingLean.Hypercube.PaperParameters.log_splitA_succ_mul_log_two_le_log_n_succ_mul_log_two {K : ℝ} {n : ℕ} :
    Real.log ((((splitA K n + 1 : ℕ) : ℝ) * Real.log 2)) ≤
      Real.log ((((n + 1 : ℕ) : ℝ) * Real.log 2)) := by sorry
