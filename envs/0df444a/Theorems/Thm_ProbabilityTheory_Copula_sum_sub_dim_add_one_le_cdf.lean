-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_sum_sub_dim_add_one_le_cdf
-- name    : ProbabilityTheory.Copula.sum_sub_dim_add_one_le_cdf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:07.228728+00:00
-- url     : https://prove2.me/theorems/4fc06b7f-81d7-456c-9d6b-15172a7d1e69
-- title:
--   Copula: sum sub dim add one le cdf
-- statement:
--   The untruncated lower Fréchet–Hoeffding bound, obtained from the union bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Bounds.lean#L29-L44
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Bounds.lean#L29-L44

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Bounds
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.sum_sub_dim_add_one_le_cdf (C : Copula d) (u : Fin d → I) :
    (∑ i, (u i : ℝ)) - d + 1 ≤ C.cdf u := by sorry
