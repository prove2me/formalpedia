-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_abs_cdf_sub_le_sum_abs
-- name    : ProbabilityTheory.Copula.abs_cdf_sub_le_sum_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:58.621345+00:00
-- url     : https://prove2.me/theorems/3a852448-a2b0-4563-a2f2-f2f65d4d67bc
-- title:
--   Copula: abs cdf sub le sum abs
-- statement:
--   A copula CDF is 1-Lipschitz for the sum of coordinate distances.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Continuity.lean#L49-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Continuity.lean#L49-L54

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Continuity
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators NNReal
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.abs_cdf_sub_le_sum_abs (C : Copula d) (u v : Fin d → I) :
    |C.cdf u - C.cdf v| ≤ ∑ i, |(u i : ℝ) - (v i : ℝ)| := by sorry
