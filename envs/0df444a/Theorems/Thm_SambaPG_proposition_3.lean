-- Prove2me | Theorems.Thm_SambaPG_proposition_3
-- name    : SambaPG.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:39:46.761954+00:00
-- url     : https://prove2.me/theorems/760b6582-e322-4106-a596-d84c0425865f
-- title:
--   Proposition 3 — excursions of $q_{a^\star}$ above $1/2$ are geometric and $q_{a^\star}(t)\to0$ almost surely
-- statement:
--   Consider SAMBA with $\alpha\in(0,1)$ on a Bernoulli bandit with a unique optimal arm, under condition (2), and let $q_{a^\star}(t)=1-p_{a^\star}(t)$ and $\sigma^{(k)}$ be the times of (11). Then:
--
--   1. (a) there is a constant $\rho<1$ such that, whenever $q_{a^\star}(0)\le1/2$,
--   $$
--   \mathbb P(\sigma^{(1)}<\infty)<\rho\quad\text{and}\quad \mathbb P(\sigma^{(k)}<\infty\mid\sigma^{(k-1)}<\infty)<\rho\ \text{ for every }k\in\mathbb N ;
--   $$
--   2. (b) for an initial vector with positive entries, $\displaystyle\sum_{t=0}^{\infty}\mathbb P\big(q_{a^\star}(t)\ge\tfrac12\big)<\infty$;
--   3. (c) for an initial vector with positive entries, with probability $1$, $q_{a^\star}(t)\to0$ as $t\to\infty$.
--
--   The event that the optimal arm's probability is at most $1/2$ is transient, and SAMBA converges to the optimal arm.
--
--   **Formalization Note** In (a) one $\rho$ serves every initial vector with $q_{a^\star}(0)\le1/2$ and every $k$, as the proof gives. Conditional probabilities given a null event are $0$. The series in (b) is a sum in $[0,\infty]$.
--
--   Differences from the source:
--
--   - reading: α ∈ (0, 1) is fixed in the algorithm box (p.4), not in the statement → hypotheses 0 < α and α < 1; reason: SAMBA is run with α ∈ (0, 1); for α ≥ 1 the update leaves the simplex (Lemma 10)
--   - generalization: α < ∆/(r⋆ − ∆), condition (2) → α (r⋆ − ∆) < ∆; reason: equivalent to (2) when r⋆ > ∆; also covers r⋆ = ∆, where the printed fraction is undefined
--   - reading: there exists a constant ρ < 1 (after "If q_{a⋆}(0) ≤ 1/2") → one ρ < 1 for all initial vectors with q_{a⋆}(0) ≤ 1/2 and all k; reason: the stronger reading; the proof gives ρ = 1 − p′δ with p′, δ independent of the start and of k
--   - generalization: the SAMBA process (from the uniform vector of the algorithm box) → (a) any initial probability vector with q_{a⋆}(0) ≤ 1/2; (b), (c) any initial vector with positive entries; reason: contains the uniform start for (b), (c); (a) is stated for other starts in the paper itself
--   - encoding: P(σ^(k) < ∞ | σ^(k−1) < ∞) for k ∈ ℕ → ProbabilityTheory.cond with the index shifted: P(σ^(k+1) < ∞ | σ^(k) < ∞) for k ∈ ℤ₊; reason: same family of inequalities; the k = 0 instance is P(σ^(1) < ∞) < ρ
--   - encoding: Σ_t P(q_{a⋆}(t) ≥ 1/2) < ∞ → a sum in [0, ∞] that is < ∞; reason: a real tsum of a divergent series would be 0
--   - generalization: the arm is drawn with distribution p(t) (p.4) using an independent uniform (p.7) → any jointly measurable rule draw(p, u) with λ{u ∈ [0, 1] : draw(p, u) = a} = p_a on the simplex; reason: every such rule gives the same law of the process; the inverse-CDF rule is one instance
--   - generalization: the leading arm is chosen at random among the maximizers of p(t) (p.7), distribution unspecified → any measurable rule lead(p, v) that returns a maximizer of p, fed by an independent uniform v; reason: the uniform choice among maximizers is one instance
--   - reading: rewards R_a(t) are independent Bernoulli(r_a) (p.6); the policy uses an independent uniform (p.7); ties are broken at random (p.7) → the arm uniforms, tie-break uniforms and rewards over all times are mutually independent; rewards are {0, 1}-valued almost surely; reason: the paper’s independent randomization, made explicit
--   - encoding: a finite set of N arms → a Fintype with at least two elements; reason: for N = 1 the gap ∆ is a maximum over the empty set; only an undefined case is excluded
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, Proposition 3, p.11 (proof pp.12–13); σ^(k) of (11), p.9

import Mathlib
import Definitions.Def_SambaPG_sambaRun
import Definitions.Def_SambaPG_IsDrawRule
import Definitions.Def_SambaPG_IsLeaderRule
import Definitions.Def_SambaPG_excursionTimes

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SambaPG

/-- **Proposition 3 (transience of `{q_{a⋆} ≥ 1/2}`).**
Denisov & Walton, arXiv:2007.10229v3, Proposition 3, p.11 (proof pp.12–13); `σ^{(k)}` of (11), p.9.

Under condition (2), with `q_{a⋆}(t) = 1 − p_{a⋆}(t)`:
* (a) there is a constant `ρ < 1` such that, if `q_{a⋆}(0) ≤ 1/2`, then `P(σ^{(1)} < ∞) < ρ` and
  `P(σ^{(k)} < ∞ | σ^{(k−1)} < ∞) < ρ` for every `k ∈ ℕ`;
* (b) `Σ_{t=0}^∞ P(q_{a⋆}(t) ≥ 1/2) < ∞`;
* (c) with probability `1`, `q_{a⋆}(t) → 0` as `t → ∞`.

**Formalization Note.** In (a) one `ρ` serves every initial vector with `q_{a⋆}(0) ≤ 1/2` and every
`k`, as the proof (p.12) gives; initial vectors range over the closed simplex `𝒫`. (b) and (c) are
stated for every initial vector with positive entries summing to `1` (Theorem 1 applies them to the
uniform one). `P(· | ·)` is `ProbabilityTheory.cond`; the sum in (b) is a sum in `[0, ∞]`.
Condition (2) is written `α (r⋆ − ∆) < ∆`; the standing assumption `α ∈ (0, 1)` is a hypothesis. -/
theorem proposition_3 {A : Type*} [Fintype A] [DecidableEq A] (B : BernoulliBandit A)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (ξ : SambaNoise B μ)
    {draw lead : (A → ℝ) → ℝ → A} (hdraw : IsDrawRule draw) (hlead : IsLeaderRule lead)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (h2 : α * (B.rStar - B.gap) < B.gap) :
    (∃ ρ : ℝ≥0∞, ρ < 1 ∧
      ∀ p₀ ∈ stdSimplex ℝ A, 1 - p₀ B.aStar ≤ 1 / 2 →
        let σ : ℕ → Ω → ℕ∞ := fun k ω =>
          sigmaExc (fun t => 1 - sambaRun ξ α draw lead p₀ t ω B.aStar) k
        μ {ω | σ 1 ω < ⊤} < ρ ∧
          ∀ k : ℕ, μ[|{ω | σ k ω < ⊤}] {ω | σ (k + 1) ω < ⊤} < ρ) ∧
    ∀ p₀ ∈ stdSimplex ℝ A, (∀ a, 0 < p₀ a) →
      (∑' t : ℕ, μ {ω | 1 / 2 ≤ 1 - sambaRun ξ α draw lead p₀ t ω B.aStar}) < ⊤ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun t => 1 - sambaRun ξ α draw lead p₀ t ω B.aStar) atTop (𝓝 0) := by sorry

end SambaPG
