-- Prove2me | Theorems.Thm_Rudin_ch06_singular_integrator_refutes
-- name    : Rudin.ch06_singular_integrator_refutes
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T17:03:40.634664+00:00
-- url     : https://prove2.me/theorems/8c0704d2-26ac-4c4e-97ac-db5ec54dfa55
-- title:
--   A singular integrator refutes the unbounded forms of Theorems 6.17, 6.21 and 6.22
-- statement:
--   In this formalization the upper and lower integrals are the ordinary `sSup`/`sInf` of sets of reals, which return the default value $0$ on a set that is unbounded in the relevant direction. Rudin's Chapter 6 assumes throughout that the integrand is bounded, and the three statements of the chapter that omit that clause — Theorem 6.17 (reduction of a Stieltjes integral to a Riemann integral with a density), Theorem 6.21 (the fundamental theorem of calculus) and Theorem 6.22 (integration by parts) — are all refuted at once by a single object.
--
--   Call a function $\alpha : \mathbb{R} \to \mathbb{R}$ a *singular integrator* if it is monotonically increasing, differentiable at every point of $[0,1]$, satisfies $\alpha(0) < \alpha(1)$, has derivative unbounded above on $[0,1]$, and has
--
--   $$\inf_{x \in [u,v]} \alpha'(x) = 0 \qquad \text{for every } 0 \le u < v \le 1 .$$
--
--   This theorem asserts that the existence of such an $\alpha$ makes all three unbounded statements false.
--
--   The mechanism is the default value of the suprema and infima. Since $\alpha$ is increasing, $\alpha' \ge 0$, so every infimum occurring in a lower sum is a genuine infimum and every term of an upper sum is nonnegative. The one-interval partition of $[0,1]$ has a single supremum, which is the supremum of an unbounded set and therefore evaluates to $0$, so the upper integral of $\alpha'$ is $0$; the dense small values force every lower sum to vanish, so the lower integral is $0$ as well. Hence $\alpha' \in \mathcal{R}$ with
--
--   $$\int_0^1 \alpha'(x)\,dx = 0 ,$$
--
--   even though $\alpha$ grows. Taking $f \equiv 1$ (which is bounded, and whose upper and lower sums telescope to $\alpha(1) - \alpha(0)$) contradicts the conclusion of Theorem 6.17; taking $F = \alpha$ contradicts Theorem 6.21; and taking $F = \alpha$, $G \equiv 1$, $g \equiv 0$ contradicts Theorem 6.22, whose right-hand side is then $\alpha(1) - \alpha(0)$ while its left-hand side is $0$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, pp. 131-134, Theorems 6.17, 6.21, 6.22 (statements taken without the boundedness hypothesis of Definition 6.2)

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- If there is a monotone, everywhere differentiable integrator `α` on `[0,1]` whose derivative
is unbounded above and takes arbitrarily small values on every nondegenerate subinterval, then the
unbounded forms of Rudin's Theorems 6.17, 6.21 and 6.22 all fail. -/
theorem ch06_singular_integrator_refutes (α : ℝ → ℝ) (hmono : Monotone α)
    (hdiff : ∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt α (deriv α x) x)
    (hgrow : α 0 < α 1)
    (hunb : ∀ K : ℝ, ∃ x ∈ Set.Icc (0:ℝ) 1, K < deriv α x)
    (hsmall : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ ε > 0, ∃ x ∈ Set.Icc u v, deriv α x < ε) :
    (¬ ∀ (a b : ℝ), a ≤ b → ∀ (f β : ℝ → ℝ), MonotoneOn β (Set.Icc a b) →
        (∀ x ∈ Set.Icc a b, HasDerivAt β (deriv β x) x) →
        RiemannIntegrable a b (deriv β) →
        (∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) →
        (RSIntegrable a b f β ↔ RiemannIntegrable a b (fun x => f x * deriv β x)) ∧
          (RSIntegrable a b f β →
            RSIntegral a b f β = RiemannIntegral a b (fun x => f x * deriv β x)))
    ∧ (¬ ∀ (a b : ℝ), a ≤ b → ∀ (f F : ℝ → ℝ), RiemannIntegrable a b f →
        (∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) → RiemannIntegral a b f = F b - F a)
    ∧ (¬ ∀ (a b : ℝ), a ≤ b → ∀ (F G f g : ℝ → ℝ),
        (∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) →
        (∀ x ∈ Set.Icc a b, HasDerivAt G (g x) x) →
        RiemannIntegrable a b f → RiemannIntegrable a b g →
        RiemannIntegral a b (fun x => F x * g x) =
          F b * G b - F a * G a - RiemannIntegral a b (fun x => f x * G x)) := by sorry

end Rudin
