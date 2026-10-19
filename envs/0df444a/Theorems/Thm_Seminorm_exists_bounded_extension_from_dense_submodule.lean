-- Prove2me | Theorems.Thm_Seminorm_exists_bounded_extension_from_dense_submodule
-- name    : Seminorm.exists_bounded_extension_from_dense_submodule
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T22:03:01.119478+00:00
-- url     : https://prove2.me/theorems/e1055965-8437-4918-b7b2-ea967e29499c
-- title:
--   Bounded linear extension from a seminorm-dense submodule
-- statement:
--   Let $V$ be a real vector space with a possibly degenerate seminorm $q$, let $S$ be a submodule dense for the distance induced by $q$, and let $F$ be a real Banach space. Every linear map $r:S\to F$ satisfying $\|r(y)\|\le Cq(y)$ extends to a linear map $T:V\to F$ satisfying the same bound. No completeness or separation is required of the domain. Density is stated explicitly as approximation to every positive real tolerance.
-- source:
--   Mathlib Analysis.Normed.Operator.Extend, LinearMap.extendOfNorm_eq and LinearMap.norm_extendOfNorm_apply_le, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Normed/Operator/Extend.lean . Seminormed-domain corollary of the bounded extension theorem.

import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Operator.Extend
open scoped NNReal
set_option autoImplicit false

theorem Seminorm.exists_bounded_extension_from_dense_submodule {V F : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (q : Seminorm ℝ V) (S : Submodule ℝ V) (r : S →ₗ[ℝ] F) (C : ℝ≥0)
    (hdense : ∀ x : V, ∀ ε : ℝ, 0 < ε → ∃ y : S, q (x - y) < ε)
    (hbound : ∀ y : S, ‖r y‖ ≤ (C : ℝ) * q y) :
    ∃ T : V →ₗ[ℝ] F, (∀ x, ‖T x‖ ≤ (C : ℝ) * q x) ∧ ∀ y : S, T y = r y := by sorry
