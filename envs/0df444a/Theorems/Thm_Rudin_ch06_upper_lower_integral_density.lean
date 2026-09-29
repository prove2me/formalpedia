-- Prove2me | Theorems.Thm_Rudin_ch06_upper_lower_integral_density
-- name    : Rudin.ch06_upper_lower_integral_density
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T15:46:22.631392+00:00
-- url     : https://prove2.me/theorems/c0959b14-cd61-4b2c-abc4-801fd6f46fc7
-- title:
--   Theorem 6.17, sharpened — upper and lower integrals against a density
-- statement:
--   A sharpening of Rudin's Theorem 6.17, in which the conclusion is separated from any integrability assumption on the integrand.
--
--   Let $\alpha$ be monotonically increasing on $[a,b]$ and differentiable at every point of $[a,b]$, with derivative $\alpha'$ bounded on $[a,b]$ and Riemann integrable there, and let $f$ be bounded on $[a,b]$. Then the upper integrals of $f$ against $d\alpha$ and of $f\alpha'$ against $dx$ coincide, and so do the two lower integrals:
--
--   $$ \overline{\int_a^b} f\,d\alpha = \overline{\int_a^b} f(x)\alpha'(x)\,dx, \qquad \underline{\int_a^b} f\,d\alpha = \underline{\int_a^b} f(x)\alpha'(x)\,dx. $$
--
--   Theorem 6.17 follows in one step: $f \in \mathcal{R}(\alpha)$ means that the two integrals on the left agree, $f\alpha' \in \mathcal{R}$ means that the two on the right agree, and the displayed identities make these conditions equivalent and identify the common values. Stating the identity at the level of upper and lower integrals is the more usable form, since it applies to an integrand that is not assumed integrable, exactly as the analogous sharpening of Theorem 6.12(c) does for additivity over adjacent intervals.
--
--   **Formalization note.** The boundedness of $\alpha'$ is stated explicitly because in this development the upper and lower integrals are ordinary suprema and infima of sets of reals, which return a default value on unbounded sets; Rudin's class $\mathcal{R}$ consists of bounded functions by convention (Definitions 6.1 and 6.2).
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 131, Theorem 6.17 (sharpened to upper and lower integrals, with the standing boundedness hypotheses of Definitions 6.1-6.2 made explicit)

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.17, sharpened: for a monotonically increasing, differentiable `α` whose
derivative is bounded and Riemann-integrable on `[a, b]`, and a bounded `f`, the upper integral of
`f dα` equals the upper integral of `f α' dx`, and the lower integrals likewise agree; no
integrability of `f` is assumed. -/
theorem ch06_upper_lower_integral_density (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hαd : ∀ x ∈ Set.Icc a b, HasDerivAt α (deriv α x) x)
    (hα' : RiemannIntegrable a b (deriv α))
    (hα'b : ∃ K, ∀ x ∈ Set.Icc a b, |deriv α x| ≤ K)
    (hf : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    upperIntegral a b f α = upperIntegral a b (fun x => f x * deriv α x) id ∧
    lowerIntegral a b f α = lowerIntegral a b (fun x => f x * deriv α x) id := by sorry

end Rudin
