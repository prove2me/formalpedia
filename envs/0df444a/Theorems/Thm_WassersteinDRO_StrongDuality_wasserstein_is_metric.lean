-- Prove2me | Theorems.Thm_WassersteinDRO_StrongDuality_wasserstein_is_metric
-- name    : WassersteinDRO.StrongDuality.wasserstein_is_metric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:58:50.818582+00:00
-- url     : https://prove2.me/theorems/717468e1-5db7-4cc5-9a6e-401812c02ceb
-- title:
--   The type-$p$ Wasserstein distance is a metric
-- statement:
--   Let $(E, \|\cdot\|)$ be a finite-dimensional real normed space with its Borel $\sigma$-algebra (the paper's $\mathbb R^m$ with an arbitrary norm), let $p \ge 1$, and let $\mathbb Q, \mathbb Q', \mathbb Q''$ be Borel probability measures on $E$. Then the type-$p$ Wasserstein distance satisfies
--
--   1. $W_p(\mathbb Q, \mathbb Q) = 0$;
--   2. $W_p(\mathbb Q, \mathbb Q') = W_p(\mathbb Q', \mathbb Q)$ (symmetry);
--   3. $W_p(\mathbb Q, \mathbb Q'') \le W_p(\mathbb Q, \mathbb Q') + W_p(\mathbb Q', \mathbb Q'')$ (subadditivity);
--   4. $W_p(\mathbb Q, \mathbb Q') = 0$ implies $\mathbb Q = \mathbb Q'$.
--
--   Nonnegativity holds because $W_p$ takes values in $[0, \infty]$. Together, these say that $W_p$ is an (extended) metric on the probability measures on $E$. In the strong duality theorem it identifies the ball of radius $0$ with the nominal distribution alone.
--
--   **Formalization Note** $W_p$ may equal $+\infty$ (the paper notes it is finite under moment conditions), so the clauses are stated in $[0, \infty]$.
--
--   Differences from the source:
--
--   - encoding: R^m with an arbitrary norm ‖·‖ → a finite-dimensional real normed space E with its Borel σ-algebra; reason: the same instances up to linear isometry
--   - encoding: a metric (nonnegative, symmetric, subadditive, vanishing only if Q = Q′) → W_p valued in [0, ∞]; the four clauses W(Q,Q) = 0, symmetry, triangle inequality, W(Q,Q′) = 0 → Q = Q′; reason: W_p can be +∞ (p. 3), so the metric is an extended metric; nonnegativity is automatic in [0, ∞]
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, §1, unnumbered sentence after Definition 1, p. 3

import Mathlib
import Definitions.Def_WassersteinDRO_StrongDuality_wasserstein

open MeasureTheory

namespace WassersteinDRO.StrongDuality

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
theorem wasserstein_is_metric {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {p : ℝ} (hp : 1 ≤ p) (Q Q' Q'' : Measure E) [IsProbabilityMeasure Q]
    [IsProbabilityMeasure Q'] [IsProbabilityMeasure Q''] :
    wasserstein p Q Q = 0 ∧ wasserstein p Q Q' = wasserstein p Q' Q ∧
      wasserstein p Q Q'' ≤ wasserstein p Q Q' + wasserstein p Q' Q'' ∧
      (wasserstein p Q Q' = 0 → Q = Q') := by sorry

end WassersteinDRO.StrongDuality
