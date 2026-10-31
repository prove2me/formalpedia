-- Prove2me | Theorems.Thm_SuperPareto_proposition_1
-- name    : SuperPareto.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:20.086986+00:00
-- url     : https://prove2.me/theorems/bcd4bc43-860f-4aae-80c6-b3dc8e001985
-- title:
--   Proposition 1, p.5 — super-Pareto iff $1/P(X>x)$ is strictly increasing and concave (corrected: $z_X$ is the essential infimum)
-- statement:
--   Let $X$ be a real random variable with essential infimum $z_X\in\mathbb R$ (i.e. $X$ is essentially bounded below and $z_X=\sup\{m: X\ge m\text{ a.s.}\}$), and let $g(x)=1/P(X>x)$.
--
--   1. $X$ is super-Pareto if and only if $g$ is strictly increasing and concave on $[z_X,\infty)$.
--   2. If moreover $X$ is regular super-Pareto, then $z_X>0$ and
--   $$
--   g(x)\le\frac{x}{z_X}\qquad\text{for all }x\ge z_X .
--   $$
--
--   The first part characterizes super-Pareto laws by their survival function alone; the second gives the tail bound used in step (d) of the proof of Theorem 1.
--
--   **Formalization Note** $z_X$ is Mathlib's `essInf X P`, and "$z_X\in\mathbb R$" is the hypothesis $\exists m,\ m\le X$ a.s. The page's formula $z_X=\inf\{z\in\mathbb R:P(X>z)>0\}$ (p.4) is a misprint and is not used. $g$ is `invSurv P X`, which Lean sets to $0$ where $P(X>x)=0$; that happens only for essentially bounded $X$, which is not super-Pareto and whose $g$ is then not strictly increasing, so the equivalence is unaffected.
--
--   Differences from the source:
--   - correction: z_X = inf{z ∈ ℝ : P(X > z) > 0} (p.4) → z_X = essInf X P, under the hypothesis that X is essentially bounded below; reason: the printed set contains every z below the essential supremum, so its infimum is −∞ for every random variable (for X ∼ Pareto(1) it is all of ℝ) and the hypothesis z_X ∈ ℝ could never hold; the words "essential infimum" and every later use of z_X (z_X = f(1), P(X > x) = 1 for x < z_X) fix the intended meaning
--   - encoding: g(x) = 1/P(X > x), +∞ where P(X > x) = 0 → invSurv P X x = 1 / P.real {X > x}, equal to 0 where P(X > x) = 0; reason: this occurs only above an essential upper bound of X; such X are not super-Pareto and their g is not strictly increasing in either convention
--   - generalization: random variables on an atomless probability space (standing assumption, p.4) → any probability space (no atomless assumption); reason: the statement depends only on joint laws; the paper's atomless case is a special case
--   - encoding: an increasing convex function f with unstated domain (Definition 1, Lemmas 1–2) → f : ℝ → ℝ, Monotone and ConvexOn ℝ univ; reason: an increasing convex function on [1, ∞) (or [0, ∞)) extends to ℝ keeping both properties and non-constancy, and only its values on the support matter
--   - encoding: random variables and events → measurable functions Ω → ℝ and measurable sets; reason: a random variable is a measurable function; Lean states measurability explicitly
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, Proposition 1, p.5 (proof in Appendix A, p.12); essential infimum, p.4

import Mathlib
import Definitions.Def_SuperPareto_IsSuperPareto
import Definitions.Def_SuperPareto_IsRegularSuperPareto
import Definitions.Def_SuperPareto_invSurv

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Proposition 1: the reciprocal survival function.** Chen, Embrechts, Wang, *An unexpected
stochastic dominance*, arXiv:2208.08471v4, Proposition 1, p.5: a random variable `X` with essential
infimum `z_X ∈ ℝ` is super-Pareto if and only if the function `g : x ↦ 1/P(X > x)` is strictly
increasing and concave on `[z_X, ∞)`. If further `X` is regular, then `z_X > 0` and `g(x) ≤ x/z_X`
for `x ≥ z_X`.

**Formalization Note.** `z_X` is Mathlib's `essInf X P`, and "`z_X ∈ ℝ`" is the hypothesis that `X`
is essentially bounded below (`∃ m, m ≤ X` a.e.), under which `essInf X P` is the true essential
infimum. The page's formula `z_X = inf{z ∈ ℝ : P(X > z) > 0}` (p.4) is a misprint (that infimum is
`−∞` for every random variable), so it is not used. `g` is `invSurv P X x = 1 / P.real {X > x}`,
which Lean sets to `0` where `P(X > x) = 0`; such `x` exist only for essentially bounded `X`, which is
neither super-Pareto nor has a strictly increasing `g`. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (hbdd : ∃ m : ℝ, ∀ᵐ ω ∂P, m ≤ X ω) :
    (IsSuperPareto P X ↔
      (StrictMonoOn (invSurv P X) (Set.Ici (essInf X P)) ∧
        ConcaveOn ℝ (Set.Ici (essInf X P)) (invSurv P X))) ∧
    (IsRegularSuperPareto P X →
      0 < essInf X P ∧ ∀ x, essInf X P ≤ x → invSurv P X x ≤ x / essInf X P) := by sorry

end SuperPareto
