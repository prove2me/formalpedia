-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_uniformContinuous_cdf
-- name    : ProbabilityTheory.Copula.uniformContinuous_cdf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:16.63818+00:00
-- url     : https://prove2.me/theorems/b4c7ab8d-4f3e-431a-b609-83630ff0a156
-- title:
--   Copula: uniform Continuous cdf
-- statement:
--   Copula CDFs are uniformly continuous on the cube.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Continuity.lean#L68-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Continuity.lean#L68-L69

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

theorem ProbabilityTheory.Copula.uniformContinuous_cdf (C : Copula d) : UniformContinuous C.cdf := by sorry
