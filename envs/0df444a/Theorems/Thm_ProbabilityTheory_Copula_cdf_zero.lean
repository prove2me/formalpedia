-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_cdf_zero
-- name    : ProbabilityTheory.Copula.cdf_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:20.642117+00:00
-- url     : https://prove2.me/theorems/0c72aeeb-1bfb-4e4a-bd9a-aee6885021c5
-- title:
--   Copula: cdf zero
-- statement:
--   The Copula construction uses the cdf zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF.lean#L65-L66
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF.lean#L65-L66

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

theorem ProbabilityTheory.Copula.cdf_zero (C : Copula d) [NeZero d] : C.cdf (fun _ => 0) = 0 := by sorry
