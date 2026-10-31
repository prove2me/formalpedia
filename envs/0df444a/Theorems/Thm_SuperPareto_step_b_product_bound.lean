-- Prove2me | Theorems.Thm_SuperPareto_step_b_product_bound
-- name    : SuperPareto.step_b_product_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:23.287178+00:00
-- url     : https://prove2.me/theorems/a5264f5b-8950-40ac-8104-738079450957
-- title:
--   Step (b), pp.8–9 — the product bound for weakly negatively associated variables
-- statement:
--   Let $X_1,\dots,X_n$ be weakly negatively associated real random variables, fix an index $k$, nonnegative weights $\theta_i$ ($i\ne k$), and thresholds $t,\delta\in\mathbb R$. Then
--
--   $$
--   P\Big(\sum_{i\ne k}\theta_iX_i\ge t,\ X_k<\delta\Big)\ \ge\ P\Big(\sum_{i\ne k}\theta_iX_i\ge t\Big)\,P(X_k<\delta).
--   $$
--
--   With $k=n$ this is the chain of displays in step (b): because $\{\mathbf y:\sum_{i\ne k}\theta_iy_i<t\}$ is a decreasing set, weak negative association bounds the joint probability of the complementary event by a product. It turns the equalities of step (a), which used independence, into inequalities.
--
--   **Formalization Note** The event $\{X_k<\delta\}$ is strict, so the bound is not literally an instance of the definition, which uses $\{X_k\le x\}$. Probabilities are real (`P.real`); the sum runs over the indices other than $k$.
--
--   Differences from the source:
--   - generalization: Y₁, …, Yₙ with the Pareto(1) law, t > 1, n ≥ 2, weights from Δₙ⁺ → a finite index type of any size (n = 1 allowed), any real laws, any t and δ, any distinguished index k, any nonnegative weights on the other indices; reason: the argument uses only weak negative association and θᵢ ≥ 0; the paper's case is a special case
--   - generalization: random variables on an atomless probability space (standing assumption, p.4) → any probability space (no atomless assumption); reason: the statement depends only on joint laws; the paper's atomless case is a special case
--   - reading: decreasing sets S ⊆ ℝ^{n−1} in Definition 2 (weak negative association) → measurable (Borel) decreasing sets in `IsWNA`; reason: P(X₋ᵢ ∈ S) is defined only for measurable S; as a hypothesis this quantifies over fewer sets, so the theorem is at least as strong
--   - encoding: P(X₋ᵢ ∈ S | Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) for x with P(Xᵢ ≤ x) > 0 (display (2)) → P(X₋ᵢ ∈ S, Xᵢ ≤ x) ≤ P(X₋ᵢ ∈ S) · P(Xᵢ ≤ x) for every x; reason: equivalent when P(Xᵢ ≤ x) > 0; when P(Xᵢ ≤ x) = 0 the product form reads 0 ≤ 0
--   - encoding: random variables and events → measurable functions Ω → ℝ and measurable sets; reason: a random variable is a measurable function; Lean states measurability explicitly
-- source:
--   Chen, Embrechts, Wang, An unexpected stochastic dominance: Pareto distributions, dependence, and diversification, arXiv:2208.08471v4, §2.3, step (b), pp.8–9, "Since {(y1, . . . , yn) : θ1y1 + · · · + θnyn < t} is a decreasing set"

import Mathlib
import Definitions.Def_SuperPareto_IsWNA

open MeasureTheory ProbabilityTheory

namespace SuperPareto

/-- **Step (b): the product bound under weak negative association.** Chen, Embrechts, Wang,
*An unexpected stochastic dominance*, arXiv:2208.08471v4, §2.3, step (b), pp.8–9, "Since
`{(y₁, …, yₙ) : θ₁y₁ + ⋯ + θₙyₙ < t}` is a decreasing set, if `Y₁, …, Yₙ` are weakly negatively
associated, for any `t > 1` and `n ≥ 2`,
`P(θ₁Y₁ + ⋯ + θ_{n−1}Y_{n−1} ≥ t; Yₙ < δ) ≥ P(θ₁Y₁ + ⋯ + θ_{n−1}Y_{n−1} ≥ t) P(Yₙ < δ)`."

Stated for a weakly negatively associated family `X : ι → Ω → ℝ`, a distinguished index `k` (the
paper's `n`), nonnegative weights `θ i` on the other indices, and any thresholds `t` and `δ`.

**Formalization Note.** The paper's step (b) is about Pareto(1) variables with `t > 1`; the bound
uses only weak negative association and `θ ≥ 0`, and holds for every real law, every `t` and every
`δ`. The event `Yₙ < δ` is strict, so the bound is not a single instance of Definition 2 (which uses
`Xᵢ ≤ x`). Probabilities are real (`P.real`). -/
theorem step_b_product_bound {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [Fintype ι] [DecidableEq ι] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hWNA : IsWNA P X) (k : ι) (θ : ι → ℝ) (hθ : ∀ i, 0 ≤ θ i)
    (t δ : ℝ) :
    P.real {ω | t ≤ ∑ i ∈ Finset.univ.erase k, θ i * X i ω} * P.real {ω | X k ω < δ} ≤
      P.real {ω | t ≤ ∑ i ∈ Finset.univ.erase k, θ i * X i ω ∧ X k ω < δ} := by sorry

end SuperPareto
