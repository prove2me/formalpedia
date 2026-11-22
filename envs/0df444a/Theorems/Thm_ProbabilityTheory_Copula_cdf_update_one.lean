-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_cdf_update_one
-- name    : ProbabilityTheory.Copula.cdf_update_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:23.033333+00:00
-- url     : https://prove2.me/theorems/1c42911b-5780-40b6-9fd5-0aba6128f5d3
-- title:
--   Copula: cdf update one
-- statement:
--   With all other coordinates equal to one, the CDF is the remaining coordinate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF.lean#L70-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF.lean#L70-L83

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

theorem ProbabilityTheory.Copula.cdf_update_one (C : Copula d) (i : Fin d) (u : I) :
    C.cdf (Function.update (fun _ => 1) i u) = (u : ℝ) := by sorry
