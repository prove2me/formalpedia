-- Prove2me | Theorems.Thm_UnivAccel_phase_cost
-- name    : UnivAccel.phase_cost
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:48.619317+00:00
-- url     : https://prove2.me/theorems/e30e9f8e-246a-4062-9b19-98ff42af67d6
-- title:
--   §5.4 Cost of a phase — one restart phase costs $O(1+(R/r)^{2/3})$ ball queries
-- statement:
--   There is an absolute constant $C > 0$ with the following property. Let $f : \mathbb R^n \to \mathbb R$ be convex and differentiable, $\mu > 0$, $R > 0$, $r > 0$, let $O$ be a radius-$r$ ball oracle for every regularized objective of $f$, and let $z$ minimize $\tilde f = f + \frac\mu2\|\cdot - a\|^2$, with
--   $$
--   \tilde f(a) - \tilde f(z) \le \mu R^2 .
--   $$
--   Run one phase of the restarted lookahead method from $a$ with zero velocity: blocks $j = 0, 1, \dots$ with $\mathcal H_j = 2^{-j}\cdot 2\mu R^2$, $h$ from (43) with $\mathcal H = \mathcal H_j$, the number of steps in (46), and the blocks stopped once $\mathcal H_j \le \mu r^2/2$. Then within $t \le C(1 + (R/r)^{2/3})$ ball queries a query returns $z$ and the phase ends there.
--
--   Summed over the $\lceil\log_2(\Delta/\varepsilon)\rceil$ restart phases, this gives the lookahead clause of Theorem 2.
--
--   Differences from the source:
--   - generalization: a phase with f(x*) = 0, f(a) > 0, ‖a‖ ≤ R and μ = f(a)/R² → any μ > 0 and anchor a with f̃(a) − f̃(z) ≤ μR²; reason: the page's cost analysis uses only H0 ≤ 2(f̃(a) − f̃(z)) ≤ 2μR²; f̃(a) − f̃(z) ≤ f(a) = μR² in the page's setting
--   - reading: O(1 + (R/r)^{2/3}) ball queries → ∃ C > 0 quantified before n, f, O, μ, R, r, a; reason: O(·) as an absolute constant
--   - encoding: "We stop the blocks once 𝓗_j ≤ μr²/2"; "the next query returns z" → after that block the phase keeps its duration and stops at the first query with ∇f̃(x_c) = 0; reason: the page proves the next query returns z, so no other stopping rule is needed
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §5.4 "Cost of a phase", pp.24–25

import Mathlib
import Definitions.Def_UnivAccel_IsBallOracle
import Definitions.Def_UnivAccel_laPhaseStep

namespace UnivAccel

/-- §5.4 "Cost of a phase", pp.24–25 (Adil–Kyng, *Universal Acceleration: New Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256 c7b64bc2…980250)): one phase of the restarted lookahead method
costs `O(1 + (R/r)^{2/3})` ball queries. Let `f` be convex and differentiable, `μ > 0`, `R > 0`,
`r > 0`, `O` a radius-`r` ball oracle for every regularized objective of `f`, and `z` the minimizer of
`f̃ = f + μ/2 ‖· − a‖²` with `f̃(a) − f̃(z) ≤ μR²`. The phase that runs the method of §5.3 on `f̃`
from `a` with zero velocity, in blocks `j = 0, 1, …` with `𝓗_j = 2^{−j}·2μR²`, `h` by (43) with
`𝓗 = 𝓗_j` and the number of steps in (46), the blocks stopped once `𝓗_j ≤ μr²/2`, ends with a query
returning `z` after at most `C(1 + (R/r)^{2/3})` ball queries, for an absolute constant `C`.

**Formalization Note** The page's phase has `μ = f(a)/R²` with `f(x*) = 0`, from which it derives
`f̃(a) − f̃(z) ≤ f(a) = μR²`; the theorem assumes only that inequality. The phase is `laPhaseStep`,
the same one the restarted method `lookRun` runs; one call is one ball query. -/
theorem phase_cost :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (O : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (μ R r : ℝ) (a z : EuclideanSpace ℝ (Fin n)),
      ConvexOn ℝ Set.univ f → Differentiable ℝ f → IsBallOracle f r O →
      0 < μ → 0 < R → 0 < r →
      (∀ y, regObj f μ a z ≤ regObj f μ a y) →
      regObj f μ a a - regObj f μ a z ≤ μ * R ^ 2 →
      ∃ t : ℕ, (t : ℝ) ≤ C * (1 + (R / r) ^ ((2 : ℝ) / 3)) ∧
        ((laPhaseStep f O μ R r a)^[t] (laPhaseInit μ R r a)).done = true ∧
        ((laPhaseStep f O μ R r a)^[t] (laPhaseInit μ R r a)).x = z := by sorry

end UnivAccel
