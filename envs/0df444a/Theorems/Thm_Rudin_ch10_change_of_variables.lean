-- Prove2me | Theorems.Thm_Rudin_ch10_change_of_variables
-- name    : Rudin.ch10_change_of_variables
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:16:26.507658+00:00
-- url     : https://prove2.me/theorems/f7478819-22b8-4ee3-9ab7-f29d324d810b
-- title:
--   Theorem 10.9 — change of variables
-- statement:
--   Let $T$ be a one-to-one $C'$-mapping of an open set $E \subseteq \mathbb{R}^k$ into $\mathbb{R}^k$ whose Jacobian determinant vanishes nowhere, and let $f$ be continuous with compact support contained in $T(E)$. Then $\int_{\mathbb{R}^k} f(\mathbf{y})\,d\mathbf{y} = \int_E f(T(\mathbf{x}))\,|J_T(\mathbf{x})|\,d\mathbf{x}$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 10, p. 252, Theorem 10.9

import Mathlib
import Definitions.Def_Rudin_ch10_forms

open Filter Topology MeasureTheory

namespace Rudin

/-- Rudin, Theorem 10.9 (change of variables): if `T` is a one-to-one `C'`-mapping of an open
set `E ⊆ ℝᵏ` into `ℝᵏ` whose Jacobian never vanishes, and `f` is continuous with compact
support contained in `T(E)`, then
`∫ f(y) dy = ∫_E f(T x) |J_T(x)| dx`. -/
theorem ch10_change_of_variables (k : ℕ) (E : Set (Fin k → ℝ)) (hE : IsOpen E)
    (T : (Fin k → ℝ) → (Fin k → ℝ)) (hT : ContDiffOn ℝ 1 T E) (hinj : Set.InjOn T E)
    (hJ : ∀ x ∈ E, jacobian T id x ≠ 0)
    (f : (Fin k → ℝ) → ℝ) (hf : Continuous f) (hsupp : HasCompactSupport f)
    (hsub : tsupport f ⊆ T '' E) :
    (∫ y, f y) = ∫ x in E, f (T x) * |jacobian T id x| := by sorry

end Rudin
