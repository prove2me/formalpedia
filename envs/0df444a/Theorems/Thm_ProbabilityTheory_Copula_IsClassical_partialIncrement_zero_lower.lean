-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsClassical_partialIncrement_zero_lower
-- name    : ProbabilityTheory.Copula.IsClassical.partialIncrement_zero_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:52:00.300568+00:00
-- url     : https://prove2.me/theorems/bf3d9221-0f63-4a1c-93a2-1007c3ee4870
-- title:
--   Is Classical: partial Increment zero lower
-- statement:
--   The Is Classical construction uses the partial Increment zero lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L60-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L60-L72

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

theorem ProbabilityTheory.Copula.IsClassical.partialIncrement_zero_lower (hF : IsClassical F)
    (a b : Fin d → I) (s : Finset (Fin d)) (ha : ∀ i ∈ s, a i = 0) :
    partialIncrement F a b s = F b := by sorry
