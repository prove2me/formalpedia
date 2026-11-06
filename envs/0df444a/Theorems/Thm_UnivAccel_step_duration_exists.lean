-- Prove2me | Theorems.Thm_UnivAccel_step_duration_exists
-- name    : UnivAccel.step_duration_exists
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:50.150128+00:00
-- url     : https://prove2.me/theorems/a074aed0-6109-471f-90f2-b3fd94a4462a
-- title:
--   §4.2 Computing $h$ — limits of $\phi$, bisection cost, and existence of a step duration
-- statement:
--   There is an absolute constant $C > 0$ with the following property. Let $f : \mathbb R^n \to \mathbb R$ be differentiable and $\mu$-strongly convex with $\mu > 0$, let $r > 0$, let $O$ be a radius-$r$ ball oracle for $f$ ($O(c)$ minimizes $f$ over the closed ball of radius $r$ around $c$), and let $(x, v)$ be any state. With
--   $$
--   x_{1/2}(h) = x + \frac{h}{1 + 2h\sqrt\mu}v, \qquad x_+(h) = O(x_{1/2}(h)), \qquad \phi(h) = \frac{h^2\|\nabla f(x_+(h))\|}{1 + 2h\sqrt\mu} - r :
--   $$
--   1. $\phi(h) \to -r$ as $h \to 0^+$, and from any trial duration $h_0 > 0$ repeated halving makes $\phi$ negative;
--   2. $x_{1/2}(h) \to x + v/(2\sqrt\mu)$ as $h \to \infty$; if the oracle's answer at this point has nonzero gradient (is not the minimizer), then $\phi(h) \to \infty$ and from any trial duration repeated doubling makes $\phi$ positive;
--   3. for durations $0 < a < b$ with $\phi(a) < 0 < \phi(b)$ and any $\varepsilon > 0$, bisection on $[a, b]$ finds a root of $\phi$ to accuracy $\varepsilon$ within $C\log(2 + (b - a)/\varepsilon)$ trials: after that many trials the bracket has length at most $\varepsilon$ and contains a root of $\phi$;
--   4. consequently some query returns the minimizer (at a duration $h > 0$ or at the limit point), or some $h > 0$ with $\nabla f(x_+(h)) \neq 0$ satisfies $\phi(h) = 0$, i.e. (17).
--
--   Item 4 is what makes the implicit Euler method well defined: from every state some step exists.
--
--   Differences from the source:
--   - reading: "bisection on [a, b] then finds a root of ϕ to accuracy ε in O(log(2 + (b − a)/ε)) further trials" → after at most C·log(2 + (b − a)/ε) trials of bisect the bracket has length ≤ ε and contains a root of ϕ; C absolute and quantified first; reason: accuracy ε read as the bracket length; O(·) as an absolute constant
--   - reading: the paragraph's conclusion that a duration solving (17) can be found → clause 4: a query returns the minimizer at some h > 0 or at the limit point, or some h > 0 with nonzero gradient solves ϕ(h) = 0; reason: the page stops when a call returns the minimizer ("if any call returns the minimizer, we stop"); otherwise the limits and continuity give a root
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §4.2 "Computing h", p.14

import Mathlib
import Definitions.Def_UnivAccel_IsBallOracle
import Definitions.Def_UnivAccel_IsIERun
import Definitions.Def_UnivAccel_bisect

open Filter Topology

namespace UnivAccel

/-- §4.2 "Computing h", p.14 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)): a step duration can be found. Let `f` be
differentiable and `μ`-strongly convex on `ℝⁿ`, `μ > 0`, `r > 0`, `O` a radius-`r` ball oracle for `f`,
and `(x, v)` any state. With `x_{1/2}(h) = x + h/(1 + 2h√μ) v`, `x₊(h) = Ball^f_r(x_{1/2}(h))` and
`ϕ(h) = h²‖∇f(x₊(h))‖/(1 + 2h√μ) − r`:
1. as `h → 0`, `ϕ(h) → −r`, and from any trial duration repeated halving makes `ϕ` negative;
2. as `h → ∞`, `x_{1/2}(h) → x + v/(2√μ)`; if the oracle's answer there has nonzero gradient (is
   not the minimizer), then `ϕ(h) → ∞` and from any trial duration repeated doubling makes `ϕ`
   positive;
3. given durations `0 < a < b` with `ϕ(a) < 0 < ϕ(b)`, bisection on `[a, b]` finds a root of `ϕ` to
   accuracy `ε` in `O(log(2 + (b − a)/ε))` further trials: after that many trials the bracket has
   length at most `ε` and contains a root of `ϕ`;
4. consequently some query of a step returns the minimizer (at a duration `h > 0` or at the
   limit point), or some `h > 0` with `∇f(x₊(h)) ≠ 0` is a root of `ϕ`, i.e. satisfies (17).

**Formalization Note** `O(·)` is an absolute constant `C > 0` quantified first; bisection is
`bisect`. -/
theorem step_duration_exists :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (μ r : ℝ)
      (O : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x v : EuclideanSpace ℝ (Fin n)),
      Differentiable ℝ f → StrongConvexOn Set.univ μ f → 0 < μ → 0 < r →
      (∀ c, IsBallMin f c r (O c)) →
      let φ : ℝ → ℝ := fun h =>
        h ^ 2 * ‖gradient f (O (ieHalf μ h x v))‖ / (1 + 2 * h * Real.sqrt μ) - r
      (Tendsto φ (𝓝[>] 0) (𝓝 (-r)) ∧ ∀ h₀ : ℝ, 0 < h₀ → ∃ k : ℕ, φ (h₀ / 2 ^ k) < 0) ∧
      Tendsto (fun h => ieHalf μ h x v) atTop (𝓝 (ieLimit μ x v)) ∧
      (gradient f (O (ieLimit μ x v)) ≠ 0 →
        Tendsto φ atTop atTop ∧ ∀ h₀ : ℝ, 0 < h₀ → ∃ k : ℕ, 0 < φ (h₀ * 2 ^ k)) ∧
      (∀ a b ε : ℝ, 0 < a → a < b → φ a < 0 → 0 < φ b → 0 < ε →
        ∃ k : ℕ, (k : ℝ) ≤ C * Real.log (2 + (b - a) / ε) ∧
          (bisect φ a b k).2 - (bisect φ a b k).1 ≤ ε ∧
          ∃ h ∈ Set.Icc (bisect φ a b k).1 (bisect φ a b k).2, φ h = 0) ∧
      ((∃ h : ℝ, 0 < h ∧ gradient f (O (ieHalf μ h x v)) = 0) ∨
        gradient f (O (ieLimit μ x v)) = 0 ∨
        ∃ h : ℝ, 0 < h ∧ gradient f (O (ieHalf μ h x v)) ≠ 0 ∧ φ h = 0) := by sorry

end UnivAccel
