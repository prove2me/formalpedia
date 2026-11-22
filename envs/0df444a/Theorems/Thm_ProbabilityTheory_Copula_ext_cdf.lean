-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_ext_cdf
-- name    : ProbabilityTheory.Copula.ext_cdf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:53.691885+00:00
-- url     : https://prove2.me/theorems/0218f827-cf23-4987-bc1e-d9694876bce6
-- title:
--   Copula: ext cdf
-- statement:
--   Two copulas are equal if their distribution functions agree at every point.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Extensionality.lean#L28-L51
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Extensionality.lean#L28-L51

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_CDF_Extensionality
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory MeasurableSpace Set
open scoped unitInterval
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.ext_cdf {C D : Copula d} (h : ∀ u, C.cdf u = D.cdf u) : C = D := by sorry
