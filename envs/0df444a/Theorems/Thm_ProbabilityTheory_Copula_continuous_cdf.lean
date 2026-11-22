-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_continuous_cdf
-- name    : ProbabilityTheory.Copula.continuous_cdf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:58.139376+00:00
-- url     : https://prove2.me/theorems/555c259f-fd37-40a0-ba0b-94c1aebc2e8d
-- title:
--   Copula: continuous cdf
-- statement:
--   Copula CDFs are continuous on the cube.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Continuity.lean#L73-L74
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Continuity.lean#L73-L74

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

theorem ProbabilityTheory.Copula.continuous_cdf (C : Copula d) : Continuous C.cdf := by sorry
