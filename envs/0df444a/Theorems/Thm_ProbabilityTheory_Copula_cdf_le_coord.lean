-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_cdf_le_coord
-- name    : ProbabilityTheory.Copula.cdf_le_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:28.789097+00:00
-- url     : https://prove2.me/theorems/75bae398-3b11-49a4-94ff-c6b142f23f4f
-- title:
--   Copula: cdf le coord
-- statement:
--   Every coordinate is an upper bound for the CDF.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF.lean#L51-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF.lean#L51-L56

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

theorem ProbabilityTheory.Copula.cdf_le_coord (C : Copula d) (u : Fin d → I) (i : Fin d) :
    C.cdf u ≤ (u i : ℝ) := by sorry
