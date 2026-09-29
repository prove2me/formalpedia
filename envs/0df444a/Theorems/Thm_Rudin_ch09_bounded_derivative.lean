-- Prove2me | Theorems.Thm_Rudin_ch09_bounded_derivative
-- name    : Rudin.ch09_bounded_derivative
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:55:43.535958+00:00
-- url     : https://prove2.me/theorems/58193f4a-2bc4-43e9-8f88-90af3e6814e6
-- title:
--   Theorem 9.19 — mean value inequality on a convex set
-- statement:
--   If $\mathbf{f}$ is differentiable on a convex open set $E$ with $\|\mathbf{f}'(\mathbf{x})\| \le M$ for all $\mathbf{x} \in E$, then $|\mathbf{f}(\mathbf{b}) - \mathbf{f}(\mathbf{a})| \le M|\mathbf{b} - \mathbf{a}|$ for all $\mathbf{a}, \mathbf{b} \in E$. Taking $M = 0$ shows a map with vanishing derivative on a convex open set is constant.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 9, p. 218, Theorem 9.19

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 9.19: if `f` is differentiable on a convex open set `E` with
`‖f'(x)‖ ≤ M` there, then `f` is Lipschitz with constant `M` on `E`; in particular a vanishing
derivative on a convex open set forces `f` to be constant. -/
theorem ch09_bounded_derivative (n m : ℕ) (E : Set (EuclideanSpace ℝ (Fin n))) (hE : IsOpen E)
    (hconv : Convex ℝ E) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (f' : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hf : ∀ x ∈ E, HasFDerivAt f (f' x) x) (M : ℝ) (hM : ∀ x ∈ E, ‖f' x‖ ≤ M) :
    ∀ a ∈ E, ∀ b ∈ E, ‖f b - f a‖ ≤ M * ‖b - a‖ := by sorry

end Rudin
