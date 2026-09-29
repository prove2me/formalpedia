-- Prove2me | Theorems.Thm_Rudin_ch06_unbounded_monotone_integrator_criterion
-- name    : Rudin.ch06_unbounded_monotone_integrator_criterion
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T17:08:28.886985+00:00
-- url     : https://prove2.me/theorems/4db3c5b4-aeab-4d5f-90ff-03d8c142f224
-- title:
--   An unbounded integrable derivative of a monotone function has integral zero and dense small values
-- statement:
--   Let $\alpha : \mathbb{R} \to \mathbb{R}$ be monotonically increasing and differentiable at every point of $[0,1]$, and suppose its derivative is unbounded above on $[0,1]$. This theorem says that if $\alpha' \in \mathcal{R}$ on $[0,1]$ then
--
--   $$\int_0^1 \alpha'(x)\,dx = 0 \qquad\text{and}\qquad \inf_{x \in [u,v]} \alpha'(x) = 0 \ \text{ for every } 0 \le u < v \le 1 .$$
--
--   The upper and lower integrals here are the ordinary supremum and infimum of sets of reals, which take the default value $0$ on a set unbounded in the relevant direction. Since $\alpha$ increases, $\alpha' \ge 0$, so every term of an upper sum is nonnegative, while the one-interval partition of $[0,1]$ produces the supremum of an unbounded set and hence the value $0$: the upper integral is exactly $0$, and integrability transports this to the lower integral.
--
--   For the second assertion, no default value intervenes in the lower sums, because $\alpha' \ge 0$ makes every infimum genuine. If the derivative were bounded below by some $\varepsilon > 0$ on a subinterval $[u,v]$, then the partition with division points $0, u, v, 1$ would have lower sum at least $\varepsilon (v-u) > 0$; the mean value theorem bounds every lower sum by the total increment $\alpha(1) - \alpha(0)$, so the lower integral is a genuine supremum and would be positive, contradicting its vanishing.
--
--   The statement is the converse half of the criterion recorded in `Rudin.ch06_singular_integrator_refutes`: a monotone integrator whose derivative is unbounded and Riemann integrable in this sense is necessarily a *singular integrator* in the sense used there. Together the two results say that the versions of Rudin's Theorems 6.17, 6.21 and 6.22 stated without the boundedness hypothesis of Definition 6.2 fail exactly when such an integrator exists.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, Definitions 6.1-6.2 and Theorem 6.17 (p. 131); the statement analyses the degenerate case left open when the boundedness hypothesis is omitted

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- For a monotone, everywhere differentiable integrator whose derivative is unbounded above on
`[0,1]`, Riemann integrability of the derivative forces the integral to vanish and the derivative
to take arbitrarily small values on every nondegenerate subinterval. -/
theorem ch06_unbounded_monotone_integrator_criterion (α : ℝ → ℝ) (hmono : Monotone α)
    (hdiff : ∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt α (deriv α x) x)
    (hunb : ∀ K : ℝ, ∃ x ∈ Set.Icc (0:ℝ) 1, K < deriv α x)
    (hint : RiemannIntegrable 0 1 (deriv α)) :
    RiemannIntegral 0 1 (deriv α) = 0 ∧
      ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∀ ε > 0, ∃ x ∈ Set.Icc u v, deriv α x < ε := by sorry

end Rudin
