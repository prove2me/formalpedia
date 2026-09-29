-- Prove2me | Theorems.Thm_Rudin_ch06_reduction_to_riemann_of_bounded
-- name    : Rudin.ch06_reduction_to_riemann_of_bounded
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T15:37:15.12374+00:00
-- url     : https://prove2.me/theorems/18cf00a0-5fc5-46c4-a533-79ccec4ecd15
-- title:
--   Theorem 6.17 — Stieltjes integrals with a density (bounded form)
-- statement:
--   Rudin's Theorem 6.17, stated with the boundedness hypotheses that Chapter 6 assumes throughout (Definitions 6.1 and 6.2).
--
--   Let $\alpha$ be monotonically increasing on $[a,b]$ and differentiable at every point of $[a,b]$, and suppose its derivative $\alpha'$ is bounded on $[a,b]$ and Riemann integrable there. Let $f$ be bounded on $[a,b]$. Then
--   $$ f \in \mathcal{R}(\alpha) \iff f\alpha' \in \mathcal{R}, $$
--   and whenever $f \in \mathcal{R}(\alpha)$,
--   $$ \int_a^b f\,d\alpha = \int_a^b f(x)\alpha'(x)\,dx. $$
--
--   **Why the boundedness of $\alpha'$ is stated explicitly.** In this development the upper and lower integrals are ordinary suprema and infima of sets of reals, which take a default value on sets that are unbounded. Rudin's convention is that a member of $\mathcal{R}$ is bounded by definition (Definition 6.1 works throughout with bounded functions), so "$\alpha' \in \mathcal{R}$" in the book already carries boundedness; here it is spelled out as a separate hypothesis, exactly as the boundedness of $f$ is.
--
--   **Proof idea.** Given $\varepsilon>0$, choose a partition $P_0$ with $U(P_0,\alpha') - L(P_0,\alpha') < \varepsilon$. On any refinement $P$ of $P_0$, the mean value theorem produces, in each subinterval, a point $t_i$ with $\Delta\alpha_i = \alpha'(t_i)\Delta x_i$, and $|\alpha'(s) - \alpha'(t_i)|$ is bounded by the oscillation of $\alpha'$ on that subinterval for every $s$ in it. Comparing the two integrands term by term gives
--   $$|U(P,f,\alpha) - U(P,f\alpha',x)| \le M\big(U(P,\alpha')-L(P,\alpha')\big) < M\varepsilon,$$
--   with $M$ a bound for $|f|$, and the same estimate for the lower sums. Passing to common refinements and letting $\varepsilon \to 0$ shows that the upper integrals of $f\,d\alpha$ and of $f\alpha'\,dx$ coincide, and likewise the lower integrals; the two assertions follow at once.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 131, Theorem 6.17 (with the standing boundedness hypotheses of Definitions 6.1-6.2 made explicit)

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.17, with the boundedness hypotheses of Chapter 6: let `α` increase
monotonically on `[a, b]` and be differentiable there, with `α'` bounded and Riemann-integrable,
and let `f` be bounded.  Then `f ∈ ℛ(α)` if and only if `f α' ∈ ℛ`, and in that case
`∫ₐᵇ f dα = ∫ₐᵇ f(x) α'(x) dx`. -/
theorem ch06_reduction_to_riemann_of_bounded (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hαd : ∀ x ∈ Set.Icc a b, HasDerivAt α (deriv α x) x)
    (hα' : RiemannIntegrable a b (deriv α))
    (hα'b : ∃ K, ∀ x ∈ Set.Icc a b, |deriv α x| ≤ K)
    (hf : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    (RSIntegrable a b f α ↔ RiemannIntegrable a b (fun x => f x * deriv α x)) ∧
    (RSIntegrable a b f α →
      RSIntegral a b f α = RiemannIntegral a b (fun x => f x * deriv α x)) := by sorry

end Rudin
