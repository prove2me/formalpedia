-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsClassical_continuous
-- name    : ProbabilityTheory.Copula.IsClassical.continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:52.758602+00:00
-- url     : https://prove2.me/theorems/3125c3a2-1cb6-4c20-8e10-5c82ae8f5576
-- title:
--   Is Classical: continuous
-- statement:
--   The Is Classical construction uses the continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L193-L193
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L193-L193

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

theorem ProbabilityTheory.Copula.IsClassical.continuous (hF : IsClassical F) : Continuous F := by sorry
