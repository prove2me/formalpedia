-- Prove2me | Theorems.Thm_SuperPareto_eq_7
-- name    : SuperPareto.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:21.514356+00:00
-- url     : https://prove2.me/theorems/08d2e646-d5ef-4f79-ae43-40c686a2fa20
-- title:
--   Display (7), p.7 — $P(\sum\theta_iY_i\ge x)>1/x$ for independent Pareto(1) losses
-- statement:
--   Let $Y_1,\dots,Y_n$ be independent random variables, each with the Pareto(1) law ($P(Y_i>y)=1/y$ for $y\ge1$), and let $(\theta_1,\dots,\theta_n)\in\Delta_n^+=\Delta_n\cap(0,1)^n$, i.e. $\theta_i\in(0,1)$ and $\sum_i\theta_i=1$. Then for every $x\in(1,\infty)$,
--
--   $$
--   P(\theta_1Y_1+\dots+\theta_nY_n\ge x)>\frac1x .
--   $$
--
--   Since $P(Y_1>x)=1/x$, this says the weighted average of independent Pareto(1) losses exceeds every level $x>1$ with strictly larger probability than a single loss; it is step (a) of the proof of Theorem 1.
--
--   **Formalization Note** Pareto(1) is `paretoMeasure 1 1`; probabilities are real (`P.real`). The condition $\theta\in\Delta_n^+$ forces $n\ge2$.
--
--   Differences from the source:
--   - generalization: random variables on an atomless probability space (standing assumption, p.4) → any probability space (no atomless assumption); reason: the statement depends only on joint laws; the paper's atomless case is a special case
--   - encoding: random variables and events → measurable functions Ω → ℝ and measurable sets; reason: a random variable is a measurable function; Lean states measurability explicitly
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, §2.3, step (a), display (7), p.7

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Display (7): independent Pareto(1) losses.** Chen, Embrechts, Wang, *An unexpected stochastic
dominance*, arXiv:2208.08471v4, §2.3, step (a), display (7), p.7: for independent
`Y₁, …, Yₙ ∼ Pareto(1)` and `(θ₁, …, θₙ) ∈ Δₙ⁺ = Δₙ ∩ (0, 1)ⁿ`,
`P(θ₁Y₁ + ⋯ + θₙYₙ ≥ x) > 1/x` for all `x ∈ (1, ∞)`.

**Formalization Note.** Pareto(1) is Mathlib's `paretoMeasure 1 1`; the index set is a `Fintype`
`ι`; `θ ∈ Δₙ⁺` is `0 < θ i < 1` for all `i` and `∑ θ i = 1` (which forces at least two indices).
Probabilities are real (`P.real`). -/
theorem eq_7 {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [Fintype ι] (Y : ι → Ω → ℝ) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hlaw : ∀ i, P.map (Y i) = paretoMeasure 1 1)
    (θ : ι → ℝ) (hθpos : ∀ i, 0 < θ i) (hθlt : ∀ i, θ i < 1) (hθsum : ∑ i, θ i = 1)
    (x : ℝ) (hx : 1 < x) :
    1 / x < P.real {ω | x ≤ ∑ i, θ i * Y i ω} := by sorry

end SuperPareto
