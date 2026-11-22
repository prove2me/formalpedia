-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_monotone_cdf
-- name    : ProbabilityTheory.Copula.monotone_cdf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:26.133934+00:00
-- url     : https://prove2.me/theorems/11c367e2-4f58-43a5-9789-e7bc38617433
-- title:
--   Copula: monotone cdf
-- statement:
--   The copula CDF is monotone in the pointwise order.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF.lean#L39-L41
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF.lean#L39-L41

module
public import Definitions.Def_LeanPool_Copula_Basic
public import Definitions.Def_LeanPool_Copula_CDF
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.monotone_cdf (C : Copula d) : Monotone C.cdf := by sorry
