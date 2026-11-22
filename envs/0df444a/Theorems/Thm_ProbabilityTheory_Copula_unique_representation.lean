-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_unique_representation
-- name    : ProbabilityTheory.Copula.unique_representation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:05.415191+00:00
-- url     : https://prove2.me/theorems/e9708792-f4fd-4e06-bbc8-66d42238e9b7
-- title:
--   Copula: unique representation
-- statement:
--   There can be at most one copula measure representing a given function.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Basic.lean#L47-L49
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Basic.lean#L47-L49

module
public import Definitions.Def_LeanPool_Copula_Rectangle
public import Definitions.Def_LeanPool_Copula_Unique
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
public import Definitions.Def_LeanPool_Copula_Classical_Basic
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.unique_representation (F : (Fin d → I) → ℝ) {C D : Copula d}
    (hC : C.cdf = F) (hD : D.cdf = F) : C = D := by sorry
