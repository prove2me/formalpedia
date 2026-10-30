-- Prove2me | Theorems.Thm_WassersteinDRO_ConvexLossP1_wasserstein_is_metric
-- name    : WassersteinDRO.ConvexLossP1.wasserstein_is_metric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:51:49.177494+00:00
-- url     : https://prove2.me/theorems/33abfd92-c6be-4596-963a-5fa31a55dffc
-- title:
--   The Wasserstein distance $W_p$ is a metric
-- statement:
--   Let $(E, \|\cdot\|)$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra, let $p \ge 1$, and let $\mathbb Q, \mathbb Q', \mathbb Q''$ be Borel probability measures on $E$. Then
--
--   1. $W_p(\mathbb Q, \mathbb Q) = 0$;
--   2. $W_p(\mathbb Q, \mathbb Q') = W_p(\mathbb Q', \mathbb Q)$ (symmetry);
--   3. $W_p(\mathbb Q, \mathbb Q'') \le W_p(\mathbb Q, \mathbb Q') + W_p(\mathbb Q', \mathbb Q'')$ (subadditivity);
--   4. $W_p(\mathbb Q, \mathbb Q') = 0$ implies $\mathbb Q = \mathbb Q'$.
--
--   Nonnegativity holds because $W_p$ takes values in $[0, \infty]$. The metric property is what makes the Wasserstein ball a neighbourhood of its centre; in particular the ball of radius $0$ consists of the centre alone.
--
--   **Formalization Note** $W_p$ may be $+\infty$, so this is an extended metric on probability measures; the four clauses hold verbatim in $[0, \infty]$.
--
--   Differences from the source:
--   - encoding: probability distributions on R^m with an arbitrary norm → Borel probability measures on a finite-dimensional real normed space E; reason: every such E is linearly isometric to (R^m, ‖·‖) for some norm, so the instances are the same.
--   - encoding: W_p a metric (nonnegative, finite only under moment conditions, p. 3) → W_p valued in [0, ∞], nonnegativity automatic, the clauses stated in [0, ∞]; reason: the paper itself notes W_p is finite only under moment conditions, so its "metric" is an extended metric.
--   - reading: "subadditive" → the triangle inequality W_p(Q, Q″) ≤ W_p(Q, Q′) + W_p(Q′, Q″); reason: this is the meaning of subadditivity for a distance in the cited [108, p. 94].
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §1, unnumbered sentence after Definition 1, p. 3

import Mathlib
import Definitions.Def_WassersteinDRO_ConvexLossP1_wasserstein

open MeasureTheory

namespace WassersteinDRO.ConvexLossP1

/-- **The Wasserstein distance is a metric.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, §1, unnumbered sentence after Definition 1, p. 3: "One can show that the Wasserstein distance
is a metric, that is, it is nonnegative, symmetric and subadditive, and it vanishes only if
Q = Q′ [108, p. 94]."

For every `p ≥ 1` and Borel probability measures `Q, Q', Q''` on `E`:
`W_p(Q, Q) = 0`; `W_p(Q, Q') = W_p(Q', Q)`; `W_p(Q, Q'') ≤ W_p(Q, Q') + W_p(Q', Q'')`; and
`W_p(Q, Q') = 0` implies `Q = Q'`.

**Formalization Note.** `(ℝ^m, ‖·‖)` with an arbitrary norm is a finite-dimensional real normed
space `E` with its Borel σ-algebra. Nonnegativity is automatic because `W_p` takes values in
`[0, ∞]`. The distance may be `∞` (p. 3: it is finite under moment conditions), so "metric" is an
extended metric; the clauses hold verbatim with values in `[0, ∞]`. -/
theorem wasserstein_is_metric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {p : ℝ} (hp : 1 ≤ p) (Q Q' Q'' : Measure E) [IsProbabilityMeasure Q]
    [IsProbabilityMeasure Q'] [IsProbabilityMeasure Q''] :
    wasserstein p Q Q = 0 ∧ wasserstein p Q Q' = wasserstein p Q' Q ∧
      wasserstein p Q Q'' ≤ wasserstein p Q Q' + wasserstein p Q' Q'' ∧
      (wasserstein p Q Q' = 0 → Q = Q') := by sorry

end WassersteinDRO.ConvexLossP1
