-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsClassical_rectangleIncrement_zero_lower
-- name    : ProbabilityTheory.Copula.IsClassical.rectangleIncrement_zero_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:43.495844+00:00
-- url     : https://prove2.me/theorems/62cc84a7-93f7-4388-99bd-cac3ca414b0d
-- title:
--   Is Classical: rectangle Increment zero lower
-- statement:
--   The Is Classical construction uses the rectangle Increment zero lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L74-L76
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L74-L76

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

theorem ProbabilityTheory.Copula.IsClassical.rectangleIncrement_zero_lower (hF : IsClassical F) (b : Fin d → I) :
    rectangleIncrement F (fun _ => 0) b = F b := by sorry
