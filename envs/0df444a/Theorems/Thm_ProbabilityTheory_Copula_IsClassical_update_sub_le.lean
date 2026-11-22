-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsClassical_update_sub_le
-- name    : ProbabilityTheory.Copula.IsClassical.update_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:42.143697+00:00
-- url     : https://prove2.me/theorems/dc99bcf8-808a-4f7b-b0a8-6564b7ab7030
-- title:
--   Is Classical: update sub le
-- statement:
--   The Is Classical construction uses the update sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L126-L140
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L126-L140

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

theorem ProbabilityTheory.Copula.IsClassical.update_sub_le (hF : IsClassical F) (u : Fin d → I)
    (i : Fin d) (t : I) (ht : u i ≤ t) :
    F (Function.update u i t) - F u ≤ (t : ℝ) - (u i : ℝ) := by sorry
