-- Prove2me | Theorems.Thm_UnivAccel_one_phase_endpoint
-- name    : UnivAccel.one_phase_endpoint
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:18:47.951851+00:00
-- url     : https://prove2.me/theorems/3db9ced1-d44b-4c19-862e-59b179c838b8
-- title:
--   §5.4 One phase — the endpoint halves the gap and does not increase the distance to $x^*$
-- statement:
--   Let $f : \mathbb R^n \to \mathbb R$ be convex and differentiable with minimizer $x^*$, let $\mu > 0$, $a \in \mathbb R^n$, and let $z$ minimize $\tilde f(x) = f(x) + \frac\mu2\|x - a\|^2$. Then
--   1. $f(z) - f(x^*) \le \tilde f(z) - f(x^*) \le \tilde f(x^*) - f(x^*) = \frac\mu2\|a - x^*\|^2$;
--   2. optimality of $z$ gives $\nabla f(z) = \mu(a - z)$, and convexity gives $\langle \nabla f(z), z - x^*\rangle \ge f(z) - f(x^*) \ge 0$;
--   3. therefore
--   $$
--   \|z - x^*\|^2 = \|a - x^*\|^2 - \|a - z\|^2 - 2\langle a - z, z - x^*\rangle \le \|a - x^*\|^2 - \|a - z\|^2 - \frac{2(f(z) - f(x^*))}{\mu} \le \|a - x^*\|^2 ;
--   $$
--   4. if moreover $\|a - x^*\| \le R$ and $\mu = (f(a) - f(x^*))/R^2$, then $\frac\mu2\|a - x^*\|^2 \le \frac12(f(a) - f(x^*))$, so the phase endpoint halves the gap.
--
--   Each restart phase therefore halves the gap without increasing the distance to the minimizer, so the same $R$ serves every phase.
--
--   Differences from the source:
--   - generalization: x* = 0, f(x*) = 0, μ = f(a)/R², ‖a‖ ≤ R → any minimizer x*, any μ > 0 and a, with the page's last step as clause 4 under ‖a − x*‖ ≤ R, μ = (f(a) − f(x*))/R²; reason: translating x* to 0 and f(x*) to 0 gives the printed chain; the restart with the gap bound Δ_k needs the general form
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §5.4 "One phase", p.24

import Mathlib
import Definitions.Def_UnivAccel_regObj

open scoped RealInnerProductSpace

namespace UnivAccel

/-- §5.4 "One phase", p.24 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)): the phase endpoint halves the gap and does not increase the
distance to the minimizer. Let `f` be convex and differentiable with minimizer `x*`, `μ > 0`, and
`z = arg min f̃` for `f̃(x) = f(x) + μ/2 ‖x − a‖²`. Then
`f(z) − f(x*) ≤ f̃(z) − f(x*) ≤ f̃(x*) − f(x*) = μ/2 ‖a − x*‖²`; optimality of `z` gives
`∇f(z) = μ(a − z)` and convexity gives `⟨∇f(z), z − x*⟩ ≥ f(z) − f(x*) ≥ 0`; therefore
`‖z − x*‖² = ‖a − x*‖² − ‖a − z‖² − 2⟨a − z, z − x*⟩ ≤ ‖a − x*‖² − ‖a − z‖² − 2(f(z) − f(x*))/μ ≤ ‖a − x*‖²`.
If moreover `‖a − x*‖ ≤ R` and `μ = (f(a) − f(x*))/R²` (the page's `μ = f(a)/R²`), then
`μ/2 ‖a − x*‖² ≤ ½(f(a) − f(x*))`.

**Formalization Note** The page normalizes `x* = 0`, `f(x*) = 0`; here the minimizer is general. -/
theorem one_phase_endpoint {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ : ℝ)
    (xstar a z : EuclideanSpace ℝ (Fin n))
    (hconv : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) (hmin : ∀ y, f xstar ≤ f y)
    (hμ : 0 < μ) (hz : ∀ y, regObj f μ a z ≤ regObj f μ a y) :
    f z - f xstar ≤ regObj f μ a z - f xstar ∧
    regObj f μ a z - f xstar ≤ regObj f μ a xstar - f xstar ∧
    regObj f μ a xstar - f xstar = μ / 2 * ‖a - xstar‖ ^ 2 ∧
    gradient f z = μ • (a - z) ∧
    ⟪gradient f z, z - xstar⟫ ≥ f z - f xstar ∧ f z - f xstar ≥ 0 ∧
    ‖z - xstar‖ ^ 2 = ‖a - xstar‖ ^ 2 - ‖a - z‖ ^ 2 - 2 * ⟪a - z, z - xstar⟫ ∧
    ‖a - xstar‖ ^ 2 - ‖a - z‖ ^ 2 - 2 * ⟪a - z, z - xstar⟫
      ≤ ‖a - xstar‖ ^ 2 - ‖a - z‖ ^ 2 - 2 * (f z - f xstar) / μ ∧
    ‖a - xstar‖ ^ 2 - ‖a - z‖ ^ 2 - 2 * (f z - f xstar) / μ ≤ ‖a - xstar‖ ^ 2 ∧
    (∀ R : ℝ, 0 < R → ‖a - xstar‖ ≤ R → μ = (f a - f xstar) / R ^ 2 →
      μ / 2 * ‖a - xstar‖ ^ 2 ≤ 1 / 2 * (f a - f xstar)) := by sorry

end UnivAccel
