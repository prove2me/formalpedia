-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_cdf_eq_zero_of_coord_eq_zero
-- name    : ProbabilityTheory.Copula.cdf_eq_zero_of_coord_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:29.240307+00:00
-- url     : https://prove2.me/theorems/2b101718-66bf-4eb5-8ba4-93adb176994b
-- title:
--   Copula: cdf eq zero of coord eq zero
-- statement:
--   A lower orthant with a zero coordinate has zero mass.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF.lean#L59-L62
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF.lean#L59-L62

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

theorem ProbabilityTheory.Copula.cdf_eq_zero_of_coord_eq_zero (C : Copula d) (u : Fin d → I)
    (i : Fin d) (hi : u i = 0) : C.cdf u = 0 := by sorry
