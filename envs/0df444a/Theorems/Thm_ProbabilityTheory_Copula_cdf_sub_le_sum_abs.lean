-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_cdf_sub_le_sum_abs
-- name    : ProbabilityTheory.Copula.cdf_sub_le_sum_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:00.629181+00:00
-- url     : https://prove2.me/theorems/0d1b94b3-3246-43fc-a1e6-e20a2591d75a
-- title:
--   Copula: cdf sub le sum abs
-- statement:
--   A one-sided version of the Lipschitz estimate for the sum metric.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Continuity.lean#L29-L46
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Continuity.lean#L29-L46

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

theorem ProbabilityTheory.Copula.cdf_sub_le_sum_abs (C : Copula d) (u v : Fin d → I) :
    C.cdf u - C.cdf v ≤ ∑ i, |(u i : ℝ) - (v i : ℝ)| := by sorry
