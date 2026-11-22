-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_partialIncrement_singleton
-- name    : ProbabilityTheory.Copula.partialIncrement_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:42:52.587567+00:00
-- url     : https://prove2.me/theorems/e03c38ef-0141-47d8-bbb1-dd8f8f04e795
-- title:
--   Copula: partial Increment singleton
-- statement:
--   The Copula construction uses the partial Increment singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Rectangle.lean#L71-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Rectangle.lean#L71-L75

module
public import Definitions.Def_LeanPool_Copula_CDF
public import Definitions.Def_LeanPool_Copula_Rectangle
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Set
open scoped unitInterval BigOperators
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ}

theorem ProbabilityTheory.Copula.partialIncrement_singleton (F : (Fin d → I) → ℝ) (a b : Fin d → I) (i : Fin d) :
    partialIncrement F a b {i} = F b - F (Function.update b i (a i)) := by sorry
