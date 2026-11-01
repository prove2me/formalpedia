-- Prove2me | Theorems.Thm_SambaPG_proposition_2
-- name    : SambaPG.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:39:35.607077+00:00
-- url     : https://prove2.me/theorems/63f882c9-17d8-428b-a988-ebb6e3840396
-- title:
--   Proposition 2 — the embedded chain $\hat q$ is a positive supermartingale with $\mathbb E[\hat q(s)]\le N/(2N+\alpha\Delta s)$
-- statement:
--   Consider SAMBA with $\alpha\in(0,1)$ on a Bernoulli bandit with $N$ arms and a unique optimal arm, under condition (2), started from a vector with positive entries summing to $1$. Let $q_{a^\star}(t)=1-p_{a^\star}(t)$, let $t_s$ be the $s$-th time at which $q_{a^\star}(t)<1/2$, and $\hat q(s)=q_{a^\star}(t_s)$. Then every $t_s$ is almost surely finite, and
--
--   1. (a) every $t_s$ is a stopping time of the history, and with $\hat H(s)$ the history at time $t_s$, $(\hat q(s))$ is a positive supermartingale with
--   $$
--   \mathbb E[\hat q(s+1)\mid\hat H(s)]-\hat q(s)\le-\frac{\alpha\Delta}{N}\,\hat q(s)^2 ;\qquad(12)
--   $$
--   2. (b) with probability $1$, $\hat q(s)\to0$ as $s\to\infty$;
--   3. (c) for every $s$,
--   $$
--   \mathbb E[\hat q(s)]\le\frac{N}{2N+\alpha\Delta s}.\qquad(13)
--   $$
--
--   While the optimal arm leads with probability above $1/2$, the probability of the other arms decays like $1/s$; (13) is the source of the $\log T$ term in the regret bound.
--
--   **Formalization Note** "Positive supermartingale" is spelled out: the $\sigma$-algebras $\hat H(s)$ increase, $\hat q(s)$ is $\hat H(s)$-measurable, integrable, positive almost surely, and satisfies (12) almost surely. The history at time $t$ is the randomness used before $t$, which fixes $p(0),\dots,p(t)$ but not the arm played at $t$, as in the computation (15)–(16).
--
--   Differences from the source:
--
--   - reading: α ∈ (0, 1) is fixed in the algorithm box (p.4), not in the statement → hypotheses 0 < α and α < 1; reason: SAMBA is run with α ∈ (0, 1); for α ≥ 1 the update leaves the simplex (Lemma 10)
--   - generalization: α < ∆/(r⋆ − ∆), condition (2) → α (r⋆ − ∆) < ∆; reason: equivalent to (2) when r⋆ > ∆; also covers r⋆ = ∆, where the printed fraction is undefined
--   - generalization: the SAMBA process (from the uniform vector of the algorithm box) → any initial vector with positive entries summing to 1; reason: contains the uniform start
--   - reading: Ĥ(s) := H(t_s) → the stopped σ-algebra at t_s of the history filtration (randomness used before time t); reason: the proof computes E[q(t_s + 1) | H(t_s)] by averaging over the arm played at t_s, (15)–(16), so H(t_s) is the past before the move at t_s
--   - generalization: the history H(t) of arms and rewards → the larger filtration of all randomness used before t; reason: the supermartingale inequality for a larger σ-algebra implies it for a smaller one by the tower property
--   - encoding: t_s defined by the sum formula, implicitly finite → t_s as the s-th visit time to {q < 1/2}, ∞ if there is none, with the conjunct that t_s is finite a.s.; q̂(s) := 0 on {t_s = ∞}; reason: the two formulas agree; finiteness is what makes q̂(s) defined
--   - encoding: positive supermartingale → stopping times, increasing σ-algebras, adapted, integrable, a.s. positive, (12) a.s.; reason: the definition spelled out
--   - generalization: the arm is drawn with distribution p(t) (p.4) using an independent uniform (p.7) → any jointly measurable rule draw(p, u) with λ{u ∈ [0, 1] : draw(p, u) = a} = p_a on the simplex; reason: every such rule gives the same law of the process; the inverse-CDF rule is one instance
--   - generalization: the leading arm is chosen at random among the maximizers of p(t) (p.7), distribution unspecified → any measurable rule lead(p, v) that returns a maximizer of p, fed by an independent uniform v; reason: the uniform choice among maximizers is one instance
--   - reading: rewards R_a(t) are independent Bernoulli(r_a) (p.6); the policy uses an independent uniform (p.7); ties are broken at random (p.7) → the arm uniforms, tie-break uniforms and rewards over all times are mutually independent; rewards are {0, 1}-valued almost surely; reason: the paper’s independent randomization, made explicit
--   - encoding: a finite set of N arms → a Fintype with at least two elements; reason: for N = 1 the gap ∆ is a maximum over the empty set; only an undefined case is excluded
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, Proposition 2, p.10, eqs. (12), (13); t_s and q̂ on p.9; Ĥ(s) on p.10

import Mathlib
import Definitions.Def_SambaPG_sambaRun
import Definitions.Def_SambaPG_IsDrawRule
import Definitions.Def_SambaPG_IsLeaderRule
import Definitions.Def_SambaPG_historyFiltration
import Definitions.Def_SambaPG_visitTime

open MeasureTheory Filter Topology

namespace SambaPG

/-- **Proposition 2 (the embedded chain `q̂` is a positive supermartingale).**
Denisov & Walton, arXiv:2007.10229v3, Proposition 2, p.10, eqs. (12), (13); `t_s`, `q̂` on p.9,
`Ĥ(s) := H(t_s)` on p.10.

Let `q_{a⋆}(t) = 1 − p_{a⋆}(t)`, let `t_s` be the `s`-th time at which `q_{a⋆}(t) < 1/2`, and
`q̂(s) = q_{a⋆}(t_s)`. Under condition (2):
0. every `t_s` is almost surely finite;
1. (a) every `t_s` is a stopping time of the history filtration, and with `Ĥ(s)` the σ-algebra of
   the past at `t_s` (an increasing family), `(q̂(s))` is adapted, integrable and positive, and
   `E[q̂(s + 1) | Ĥ(s)] − q̂(s) ≤ −(α∆/N) q̂(s)²` (12);
2. (b) with probability `1`, `q̂(s) → 0` as `s → ∞`;
3. (c) `E[q̂(s)] ≤ N/(2N + α∆s)` for every `s` (13).

**Formalization Note.** The run starts from any vector with positive entries summing to `1`
(Theorem 1 uses the uniform one). `Ĥ(s)` is the stopped σ-algebra of the history filtration at
`t_s`; the history at time `t` is the randomness used before `t`, which determines `p(0), …, p(t)`,
so `E[· | Ĥ(s)]` averages over the arm played at time `t_s`, as in the computation (15)–(16) on p.10.
`q̂(s)` is set to `0` on the null event `t_s = ∞`. Condition (2) is written `α (r⋆ − ∆) < ∆`; the
standing assumption `α ∈ (0, 1)` is a hypothesis. -/
theorem proposition_2 {A : Type*} [Fintype A] [DecidableEq A] (B : BernoulliBandit A)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (ξ : SambaNoise B μ)
    {draw lead : (A → ℝ) → ℝ → A} (hdraw : IsDrawRule draw) (hlead : IsLeaderRule lead)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (h2 : α * (B.rStar - B.gap) < B.gap)
    {p₀ : A → ℝ} (hp₀ : p₀ ∈ stdSimplex ℝ A) (hp₀pos : ∀ a, 0 < p₀ a) :
    let q : Ω → ℕ → ℝ := fun ω t => 1 - sambaRun ξ α draw lead p₀ t ω B.aStar
    let ts : ℕ → Ω → WithTop ℕ := fun s ω => visitTime (q ω) s
    let qhat : ℕ → Ω → ℝ := fun s ω => embedded (q ω) s
    let N : ℝ := Fintype.card A
    (∀ s, ∀ᵐ ω ∂μ, ts s ω ≠ ⊤) ∧
    (∃ hT : ∀ s, IsStoppingTime (historyFiltration ξ) (ts s),
      Monotone (fun s => (hT s).measurableSpace) ∧
      ∀ s, Measurable[(hT s).measurableSpace] (qhat s) ∧ Integrable (qhat s) μ ∧
        (∀ᵐ ω ∂μ, 0 < qhat s ω) ∧
        μ[qhat (s + 1) | (hT s).measurableSpace]
          ≤ᵐ[μ] fun ω => qhat s ω - α * B.gap / N * qhat s ω ^ 2) ∧
    (∀ᵐ ω ∂μ, Tendsto (fun s => qhat s ω) atTop (𝓝 0)) ∧
    ∀ s : ℕ, ∫ ω, qhat s ω ∂μ ≤ N / (2 * N + α * B.gap * s) := by sorry

end SambaPG
