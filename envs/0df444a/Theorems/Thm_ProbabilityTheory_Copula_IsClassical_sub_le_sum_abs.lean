-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsClassical_sub_le_sum_abs
-- name    : ProbabilityTheory.Copula.IsClassical.sub_le_sum_abs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:48.331969+00:00
-- url     : https://prove2.me/theorems/9f267316-1d75-4236-8337-ef08e4b01050
-- title:
--   Is Classical: sub le sum abs
-- statement:
--   The Is Classical construction uses the sub le sum abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L159-L170
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L159-L170

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

theorem ProbabilityTheory.Copula.IsClassical.sub_le_sum_abs (hF : IsClassical F) (a b : Fin d → I) :
    F a - F b ≤ ∑ i, |(a i : ℝ) - (b i : ℝ)| := by sorry
