-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsClassical_lipschitzWith
-- name    : ProbabilityTheory.Copula.IsClassical.lipschitzWith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:58.833296+00:00
-- url     : https://prove2.me/theorems/1dda7ad6-6033-406f-b4b5-c46aac7fddc8
-- title:
--   Is Classical: lipschitz With
-- statement:
--   The Is Classical construction uses the lipschitz With property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L182-L191
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L182-L191

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

theorem ProbabilityTheory.Copula.IsClassical.lipschitzWith (hF : IsClassical F) : LipschitzWith (d : ℝ≥0) F := by sorry
