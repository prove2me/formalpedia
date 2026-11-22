-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsClassical_rectangleIncrement_mono_upper
-- name    : ProbabilityTheory.Copula.IsClassical.rectangleIncrement_mono_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:55.592021+00:00
-- url     : https://prove2.me/theorems/ca1b5b5f-9f85-4903-9e05-0e56d3a2ea6a
-- title:
--   Is Classical: rectangle Increment mono upper
-- statement:
--   Rectangle mass increases when its upper endpoint increases.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L106-L118
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L106-L118

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

theorem ProbabilityTheory.Copula.IsClassical.rectangleIncrement_mono_upper (hF : IsClassical F)
    (a b c : Fin d → I) (hab : a ≤ b) (hbc : b ≤ c) :
    rectangleIncrement F a b ≤ rectangleIncrement F a c := by sorry
