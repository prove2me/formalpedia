-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_lipschitzWith_cdf
-- name    : ProbabilityTheory.Copula.lipschitzWith_cdf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:51.749824+00:00
-- url     : https://prove2.me/theorems/1f7a1834-3765-48b1-8065-647e7ec9f879
-- title:
--   Copula: lipschitz With cdf
-- statement:
--   For Lean's default maximum metric on the cube, the Lipschitz constant is `d`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Continuity.lean#L57-L65
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Continuity.lean#L57-L65

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

theorem ProbabilityTheory.Copula.lipschitzWith_cdf (C : Copula d) : LipschitzWith (d : ℝ≥0) C.cdf := by sorry
