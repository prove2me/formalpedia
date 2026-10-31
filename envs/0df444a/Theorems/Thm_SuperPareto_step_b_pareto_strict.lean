-- Prove2me | Theorems.Thm_SuperPareto_step_b_pareto_strict
-- name    : SuperPareto.step_b_pareto_strict
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:18.97532+00:00
-- url     : https://prove2.me/theorems/a2572b0c-a2f4-4aba-bb95-d80d1f0a50ff
-- title:
--   Step (b), p.9 — weakly negatively associated Pareto(1) losses: $P(\sum\theta_iY_i>x)>1/x$
-- statement:
--   Let $Y_1,\dots,Y_n$ be weakly negatively associated random variables, each with the Pareto(1) law, and $(\theta_1,\dots,\theta_n)\in\Delta_n^+$ ($\theta_i\in(0,1)$, $\sum\theta_i=1$). Then for every $x\in(1,\infty)$,
--
--   $$
--   P(\theta_1Y_1+\dots+\theta_nY_n>x)>\frac1x=P(Y>x),\qquad Y\sim\mathrm{Pareto}(1).
--   $$
--
--   Since $P(Y>x)\in(0,1)$ exactly when $x>1$, this is the strict dominance $Y<_{\mathrm{st}}\sum_i\theta_iY_i$ that step (c) quotes ("it is shown in the previous steps that $Y<_{\mathrm{st}}\sum\theta_iY_i$"). It is the Pareto(1) case of Theorem 1(i) under weak negative association.
--
--   **Formalization Note** Pareto(1) is `paretoMeasure 1 1`; probabilities are real (`P.real`).
--
--   Differences from the source:
--   - reading: "Hence, (4) holds for weakly negatively associated Pareto(1) random variables" → the form (7) reduces it to: θ ∈ Δₙ⁺ and levels x > 1; reason: step (a) says it suffices to show (7), and step (b) re-runs that proof; levels x ≤ 1 are trivial, and (4) for every θ ∈ Δₙ for these variables is `eq_10` with f = id
--   - generalization: display (7) for weakly negatively associated Y: P(θ₁Y₁ + ⋯ + θₙYₙ ≥ x) > 1/x → P(θ₁Y₁ + ⋯ + θₙYₙ > x) > 1/x; reason: P(S > x) ≤ P(S ≥ x), so the strict-event form implies the printed one; it is the form Y <st ∑θᵢYᵢ that step (c) quotes as shown
--   - generalization: random variables on an atomless probability space (standing assumption, p.4) → any probability space (no atomless assumption); reason: the statement depends only on joint laws; the paper's atomless case is a special case
--   - reading: decreasing sets S ⊆ ℝ^{n−1} in Definition 2 (weak negative association) → measurable (Borel) decreasing sets in `IsWNA`; reason: P(X₋ᵢ ∈ S) is defined only for measurable S; as a hypothesis this quantifies over fewer sets, so the theorem is at least as strong
--   - encoding: P(X₋ᵢ ∈ S | Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) for x with P(Xᵢ ≤ x) > 0 (display (2)) → P(X₋ᵢ ∈ S, Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) · P(Xᵢ ≤ x) for every x; reason: equivalent when P(Xᵢ ≤ x) > 0; when P(Xᵢ ≤ x) = 0 the product form reads 0 ≤ 0
--   - encoding: random variables and events → measurable functions Ω → ℝ and measurable sets; reason: a random variable is a measurable function; Lean states measurability explicitly
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, §2.3, step (b), p.9, "Hence, (4) holds for weakly negatively associated Pareto(1) random variables"; step (c), p.9, "it is shown in the previous steps that Y <st ∑θiYi"

import Mathlib
import Definitions.Def_SuperPareto_IsWNA

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Step (b): weakly negatively associated Pareto(1) losses, strict form.** Chen, Embrechts,
Wang, *An unexpected stochastic dominance*, arXiv:2208.08471v4, §2.3, step (b), p.9, "Hence, (4)
holds for weakly negatively associated Pareto(1) random variables", in the strict form quoted in
step (c), p.9, "it is shown in the previous steps that `Y <st ∑ θᵢYᵢ`".

For weakly negatively associated `Y₁, …, Yₙ ∼ Pareto(1)` and `(θ₁, …, θₙ) ∈ Δₙ⁺`, every
`x ∈ (1, ∞)` satisfies `P(θ₁Y₁ + ⋯ + θₙYₙ > x) > 1/x = P(Y > x)`.

**Formalization Note.** Pareto(1) is Mathlib's `paretoMeasure 1 1`; `θ ∈ Δₙ⁺` is `0 < θ i < 1` and
`∑ θ i = 1`. The event is the strict `> x`, which implies display (7)'s `≥ x` form under weak
negative association. Since `P(Y > x) = 1/x ∈ (0, 1)` exactly for `x > 1`, this is
`Y <st ∑ θᵢYᵢ`. Probabilities are real (`P.real`). -/
theorem step_b_pareto_strict {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [Fintype ι] (Y : ι → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hWNA : IsWNA P Y) (hlaw : ∀ i, P.map (Y i) = paretoMeasure 1 1)
    (θ : ι → ℝ) (hθpos : ∀ i, 0 < θ i) (hθlt : ∀ i, θ i < 1) (hθsum : ∑ i, θ i = 1)
    (x : ℝ) (hx : 1 < x) :
    1 / x < P.real {ω | x < ∑ i, θ i * Y i ω} := by sorry

end SuperPareto
