-- Prove2me | Theorems.Thm_Rudin_ch06_reduction_to_riemann
-- name    : Rudin.ch06_reduction_to_riemann
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-12T23:22:31.026092+00:00
-- url     : https://prove2.me/theorems/2c850d16-16c1-4447-99da-dfd3e80262b5
-- title:
--   Theorem 6.17 — reduction to a Riemann integral
-- statement:
--   Let $\alpha$ increase monotonically on $[a,b]$, be differentiable there with $\alpha' \in \mathcal{R}$, and let $f$ be bounded. Then $f \in \mathcal{R}(\alpha)$ if and only if $f\alpha' \in \mathcal{R}$, and in that case $\int_a^b f\,d\alpha = \int_a^b f(x)\alpha'(x)\,dx$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 131, Theorem 6.17

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.17: let `α` increase monotonically with `α'` Riemann-integrable on
`[a, b]`, and let `f` be bounded.  Then `f ∈ ℛ(α)` if and only if `f α' ∈ ℛ`, and in that
case `∫ f dα = ∫ f α' dx`. -/
theorem ch06_reduction_to_riemann (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hαd : ∀ x ∈ Set.Icc a b, HasDerivAt α (deriv α x) x)
    (hα' : RiemannIntegrable a b (deriv α))
    (hf : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    (RSIntegrable a b f α ↔ RiemannIntegrable a b (fun x => f x * deriv α x)) ∧
    (RSIntegrable a b f α →
      RSIntegral a b f α = RiemannIntegral a b (fun x => f x * deriv α x)) := by sorry

end Rudin
