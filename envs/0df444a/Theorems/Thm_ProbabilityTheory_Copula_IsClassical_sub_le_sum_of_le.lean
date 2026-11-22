-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsClassical_sub_le_sum_of_le
-- name    : ProbabilityTheory.Copula.IsClassical.sub_le_sum_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:59.397796+00:00
-- url     : https://prove2.me/theorems/d5858f24-522a-4603-a12d-5738177f3faa
-- title:
--   Is Classical: sub le sum of le
-- statement:
--   The Is Classical construction uses the sub le sum of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L142-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L142-L157

module
public import Definitions.Def_LeanPool_Copula_Classical_Basic
public import Definitions.Def_LeanPool_Copula_Classical_Regularity
set_option autoImplicit true
@[expose] public section
public section
open Set
open scoped unitInterval BigOperators NNReal
open ProbabilityTheory ProbabilityTheory.Copula
variable {d : ℕ} {F : (Fin d → I) → ℝ}

theorem ProbabilityTheory.Copula.IsClassical.sub_le_sum_of_le (hF : IsClassical F) (a b : Fin d → I) (hab : a ≤ b) :
    F b - F a ≤ ∑ i, ((b i : ℝ) - (a i : ℝ)) := by sorry
