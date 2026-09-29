-- Prove2me | Theorems.Thm_Rudin_ch06_stieltjes_integration_by_parts
-- name    : Rudin.ch06_stieltjes_integration_by_parts
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T20:00:27.691401+00:00
-- url     : https://prove2.me/theorems/ca6c81f4-38bb-40bb-bf75-a969688ba2f4
-- title:
--   Theorem 6.22, Stieltjes form — integration by parts for two increasing functions
-- statement:
--   Let $a \le b$ and let $f$ and $\alpha$ be two real functions, each monotonically increasing on $[a,b]$. Then, with $U$ and $L$ the upper and lower Riemann–Stieltjes integrals of Rudin's Definition 6.2,
--
--   $$\overline{\int_a^b} f\,d\alpha \;+\; \underline{\int_a^b} \alpha\,df \;=\; f(b)\alpha(b) - f(a)\alpha(a),
--   \qquad
--   \underline{\int_a^b} f\,d\alpha \;+\; \overline{\int_a^b} \alpha\,df \;=\; f(b)\alpha(b) - f(a)\alpha(a).$$
--
--   Consequently $f \in \mathcal{R}(\alpha)$ on $[a,b]$ if and only if $\alpha \in \mathcal{R}(f)$ on $[a,b]$, and when this holds the two integrals satisfy the integration-by-parts identity
--
--   $$\int_a^b f\,d\alpha \;+\; \int_a^b \alpha\,df \;=\; f(b)\alpha(b) - f(a)\alpha(a).$$
--
--   This is the Stieltjes form of Rudin's Theorem 6.22: no differentiability is assumed of either function, and the roles of integrand and integrator are symmetric. The mechanism is Abel summation on a single partition $a = x_0 \le x_1 \le \dots \le x_n = b$: since both functions increase, the supremum of $f$ on $[x_{i-1},x_i]$ is $f(x_i)$ and the infimum of $\alpha$ there is $\alpha(x_{i-1})$, so
--
--   $$U(P,f,\alpha) + L(P,\alpha,f) = \sum_{i=1}^{n}\bigl(f(x_i)\alpha(x_i) - f(x_{i-1})\alpha(x_{i-1})\bigr) = f(b)\alpha(b) - f(a)\alpha(a),$$
--
--   and symmetrically for $L(P,f,\alpha) + U(P,\alpha,f)$. Taking the infimum over $P$ on one side is the same as taking the supremum on the other, which gives the two displayed identities.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6: Theorem 6.22 (p. 134) in its Stieltjes form; compare Exercise 6.17 (p. 141), which states the duality between f in R(alpha) and alpha in R(f) together with the same identity.

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.22 in Stieltjes form (integration by parts for two monotonically
increasing functions).  For `f` and `α` monotonically increasing on `[a, b]`, Abel summation
turns every upper sum for `f dα` into the complement of a lower sum for `α df`, so the upper
and lower integrals of `f dα` and of `α df` add up to `f(b)α(b) - f(a)α(a)`; in particular
`f ∈ ℛ(α)` if and only if `α ∈ ℛ(f)`, and then
`∫ₐᵇ f dα + ∫ₐᵇ α df = f(b)α(b) - f(a)α(a)`. -/
theorem ch06_stieltjes_integration_by_parts (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hf : MonotoneOn f (Set.Icc a b)) (hα : MonotoneOn α (Set.Icc a b)) :
    upperIntegral a b f α + lowerIntegral a b α f = f b * α b - f a * α a ∧
      lowerIntegral a b f α + upperIntegral a b α f = f b * α b - f a * α a ∧
      (RSIntegrable a b f α ↔ RSIntegrable a b α f) ∧
      (RSIntegrable a b f α →
        RSIntegral a b f α + RSIntegral a b α f = f b * α b - f a * α a) := by sorry

end Rudin
