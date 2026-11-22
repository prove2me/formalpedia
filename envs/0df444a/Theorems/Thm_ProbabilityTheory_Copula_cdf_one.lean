-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_cdf_one
-- name    : ProbabilityTheory.Copula.cdf_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:16.228995+00:00
-- url     : https://prove2.me/theorems/c7dbc2ce-658f-4b46-b136-2b0b067fbb35
-- title:
--   Copula: cdf one
-- statement:
--   The Copula construction uses the cdf one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF.lean#L44-L48
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/CDF.lean#L44-L48

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

theorem ProbabilityTheory.Copula.cdf_one (C : Copula d) : C.cdf (fun _ => 1) = 1 := by sorry
