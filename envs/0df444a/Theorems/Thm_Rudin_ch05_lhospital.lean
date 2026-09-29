-- Prove2me | Theorems.Thm_Rudin_ch05_lhospital
-- name    : Rudin.ch05_lhospital
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T23:08:40.540051+00:00
-- url     : https://prove2.me/theorems/284cea74-a06f-4617-b542-18974958ea72
-- title:
--   Theorem 5.13 — L'Hospital's rule, the $0/0$ case
-- statement:
--   Suppose $f$ and $g$ are differentiable on $(a,b)$ with $g' \ne 0$ there, that $f'(x)/g'(x) \to A$ as $x \to a^+$, and that $f(x) \to 0$ and $g(x) \to 0$ as $x \to a^+$. Then $f(x)/g(x) \to A$ as $x \to a^+$. This is the first of the two cases of Rudin's theorem; the case $g(x) \to \infty$ is not part of this mission.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 5, p. 109, Theorem 5.13

import Mathlib

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 5.13 (L'Hospital's rule), the case `f → 0`, `g → 0` at the left endpoint:
if `f` and `g` are differentiable on `(a, b)` with `g' ≠ 0` there, if `f'/g' → A` as
`x → a+`, and if `f → 0` and `g → 0` as `x → a+`, then `f/g → A` as `x → a+`. -/
theorem ch05_lhospital (a b : ℝ) (hab : a < b) (f g : ℝ → ℝ) (A : ℝ)
    (hfd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ f x)
    (hgd : ∀ x ∈ Set.Ioo a b, DifferentiableAt ℝ g x)
    (hg' : ∀ x ∈ Set.Ioo a b, deriv g x ≠ 0)
    (hratio : Tendsto (fun x => deriv f x / deriv g x) (𝓝[>] a) (𝓝 A))
    (hf0 : Tendsto f (𝓝[>] a) (𝓝 0)) (hg0 : Tendsto g (𝓝[>] a) (𝓝 0)) :
    Tendsto (fun x => f x / g x) (𝓝[>] a) (𝓝 A) := by sorry

end Rudin
