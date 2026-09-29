-- Prove2me | Theorems.Thm_Rudin_ch06_reduction_to_riemann_needs_integrable_derivative
-- name    : Rudin.ch06_reduction_to_riemann_needs_integrable_derivative
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T19:36:14.492319+00:00
-- url     : https://prove2.me/theorems/5403f19e-1c69-4ab6-9d9f-588ccae52377
-- title:
--   Theorem 6.17 fails without the integrability of $\alpha'$
-- statement:
--   Rudin's Theorem 6.17 (*Principles of Mathematical Analysis*, 3rd edition, Theorem 6.17) reduces a Stieltjes integral to a Riemann integral with a density: if $\alpha$ increases monotonically, $\alpha' \in \mathcal{R}$ on $[a,b]$ and $f$ is bounded, then $f \in \mathcal{R}(\alpha)$ if and only if $f\alpha' \in \mathcal{R}$, and in that case
--   $$\int_a^b f\,d\alpha = \int_a^b f(x)\,\alpha'(x)\,dx.$$
--
--   This statement asserts that the hypothesis $\alpha' \in \mathcal{R}$ is *indispensable*: it cannot be weakened to "$\alpha$ is differentiable on $[a,b]$ with bounded derivative", even though all the boundedness hypotheses of Chapter 6 are then in force. Precisely, there exists $\alpha : \mathbb{R} \to \mathbb{R}$ such that
--
--   1. $\alpha$ is monotonically increasing on $[0,1]$;
--   2. $\alpha$ is differentiable at every point of $[0,1]$;
--   3. $\alpha'$ is bounded on $[0,1]$;
--   4. $\alpha' \notin \mathcal{R}$ on $[0,1]$;
--   5. the bounded integrand $f \equiv 1$ satisfies $f \in \mathcal{R}(\alpha)$, while $f\alpha' = \alpha' \notin \mathcal{R}$.
--
--   Clauses 1-3 are exactly the hypotheses of Theorem 6.17 with $\alpha' \in \mathcal{R}$ deleted, and clause 5 is the failure of its conclusion, so the theorem is sharp in this respect.
--
--   Such an $\alpha$ exists by a construction of Volterra type. Delete from $[0,1]$ a small interval around each rational, with the total length of the deleted intervals less than $\tfrac14$; the remaining closed set $K$ has empty interior and measure at least $\tfrac34$. On each interval $(a,b)$ complementary to $K$ place the bump
--   $$g_{a,b}(y) = \left(\frac{(y-a)(b-y)}{b-a}\right)^{2}\sin\!\left(\frac{1}{y-a}\right),$$
--   which vanishes to second order at both endpoints — so the assembled function is differentiable with derivative $0$ at every point of $K$ — while its derivative oscillates between values arbitrarily close to $-1$ and to $1$ as $y \downarrow a$. Adding $2x$ makes the assembled function increasing with derivative bounded by $4$. Its derivative then oscillates by at least $1$ on every subinterval meeting $K$, so every partition $P$ of $[0,1]$ satisfies $U(P,\alpha') - L(P,\alpha') \ge \tfrac34$ and $\alpha' \notin \mathcal{R}$, whereas the sums of the constant integrand $1$ against $\alpha$ telescope, so $1 \in \mathcal{R}(\alpha)$ with $\int_0^1 1\,d\alpha = \alpha(1)-\alpha(0)$.
--
--   Some such construction is unavoidable: by Lebesgue's criterion a bounded derivative fails to be Riemann integrable exactly when its set of discontinuities has positive measure, which forces the discontinuity set to contain a nowhere dense closed set of positive measure.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, Chapter 6, Theorem 6.17 (p. 133); the counterexample is of the type introduced by V. Volterra, Giornale di Matematiche 19 (1881), 76-86.

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.17, sharpness: the hypothesis `α' ∈ ℛ` cannot be dropped, even with all
the boundedness hypotheses of Chapter 6 in force.  There is a monotonically increasing `α`,
differentiable at every point of `[0,1]` with bounded derivative, whose derivative is not
Riemann integrable, while the bounded integrand `f = 1` satisfies `f ∈ ℛ(α)`. -/
theorem ch06_reduction_to_riemann_needs_integrable_derivative :
    ∃ α : ℝ → ℝ,
      MonotoneOn α (Set.Icc 0 1) ∧
      (∀ x ∈ Set.Icc (0:ℝ) 1, HasDerivAt α (deriv α x) x) ∧
      (∃ K, ∀ x ∈ Set.Icc (0:ℝ) 1, |deriv α x| ≤ K) ∧
      ¬ RiemannIntegrable 0 1 (deriv α) ∧
      RSIntegrable 0 1 (fun _ => (1:ℝ)) α ∧
      ¬ RiemannIntegrable 0 1 (fun x => (1:ℝ) * deriv α x) := by sorry

end Rudin
