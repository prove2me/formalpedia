-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_cdf_eq_iff
-- name    : ProbabilityTheory.Copula.cdf_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:43:15.358945+00:00
-- url     : https://prove2.me/theorems/ae6e62fa-9b1c-4840-871f-18c15592ae1d
-- title:
--   Copula: cdf eq iff
-- statement:
--   The Copula construction uses the cdf eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Extensionality.lean#L57-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF/Extensionality.lean#L57-L58

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

theorem ProbabilityTheory.Copula.cdf_eq_iff {C D : Copula d} : C.cdf = D.cdf ↔ C = D := by sorry
