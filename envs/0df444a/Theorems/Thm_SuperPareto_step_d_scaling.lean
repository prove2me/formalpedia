-- Prove2me | Theorems.Thm_SuperPareto_step_d_scaling
-- name    : SuperPareto.step_d_scaling
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:16.899434+00:00
-- url     : https://prove2.me/theorems/cc550761-1ac1-4fb8-919a-b20ceb5f40da
-- title:
--   Step (d), p.10 — $g(t/c)\le g(t)/c$ for regular super-Pareto $X$
-- statement:
--   Let $X$ be a regular super-Pareto random variable and $g(x)=1/P(X>x)$. Then
--
--   $$
--   g(t/c)\le\frac{g(t)}{c}\qquad\text{for all }t\ge0\text{ and }c\in(0,1].
--   $$
--
--   This scaling property of the tail of a regular super-Pareto loss is what proves display (11), and through it part (ii) of Theorem 1.
--
--   **Formalization Note** $g$ is `invSurv P X`, defined on all of $\mathbb R$; as on p.10 it equals $1$ below the essential infimum $z_X$ ("$P(X>x)=1$ for $x<z_X$").
--
--   Differences from the source:
--   - generalization: random variables on an atomless probability space (standing assumption, p.4) → any probability space (no atomless assumption); reason: the statement depends only on joint laws; the paper's atomless case is a special case
--   - encoding: an increasing convex function f with unstated domain (Definition 1, Lemmas 1–2) → f : ℝ → ℝ, Monotone and ConvexOn ℝ univ; reason: an increasing convex function on [1, ∞) (or [0, ∞)) extends to ℝ keeping both properties and non-constancy, and only its values on the support matter
--   - encoding: random variables and events → measurable functions Ω → ℝ and measurable sets; reason: a random variable is a measurable function; Lean states measurability explicitly
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, §2.3, step (d), p.10, "together imply g(t/c) ≤ g(t)/c for t ≥ 0 and c ∈ (0, 1]"

import Mathlib
import Definitions.Def_SuperPareto_IsRegularSuperPareto
import Definitions.Def_SuperPareto_invSurv

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Step (d): scaling of the reciprocal survival function.** Chen, Embrechts, Wang, *An
unexpected stochastic dominance*, arXiv:2208.08471v4, §2.3, step (d), p.10, "As `X` is regular,
`z_X > 0`, the concavity of `g`, and `g(x) ≤ x/z_X` for `x ≥ z_X` together imply `g(t/c) ≤ g(t)/c`
for `t ≥ 0` and `c ∈ (0, 1]`."

For a regular super-Pareto `X` and `g(x) = 1/P(X > x)`, `g(t/c) ≤ g(t)/c` for all `t ≥ 0` and
`c ∈ (0, 1]`.

**Formalization Note.** `g` is `invSurv P X`, defined on all of `ℝ` (equal to `1` below the
essential infimum, as on p.10: "`P(X > x) = 1` for `x < z_X`"). -/
theorem step_d_scaling {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (hreg : IsRegularSuperPareto P X)
    (t c : ℝ) (ht : 0 ≤ t) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    invSurv P X (t / c) ≤ invSurv P X t / c := by sorry

end SuperPareto
