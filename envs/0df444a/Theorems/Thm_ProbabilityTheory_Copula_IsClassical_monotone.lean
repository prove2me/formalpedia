-- Prove2me | Theorems.Thm_ProbabilityTheory_Copula_IsClassical_monotone
-- name    : ProbabilityTheory.Copula.IsClassical.monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:51:58.654184+00:00
-- url     : https://prove2.me/theorems/f0633fd5-2b19-49db-b2d0-c78ad8406d0d
-- title:
--   Is Classical: monotone
-- statement:
--   Coordinatewise monotonicity follows from the rectangle condition.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L121-L124
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Classical/Regularity.lean#L121-L124

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

theorem ProbabilityTheory.Copula.IsClassical.monotone (hF : IsClassical F) : Monotone F := by sorry
