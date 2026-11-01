-- Prove2me | Theorems.Thm_SambaPG_lemma_6
-- name    : SambaPG.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:39:19.705508+00:00
-- url     : https://prove2.me/theorems/5f489264-c0b2-4826-be6f-c34be3e97e98
-- title:
--   Lemma 6 — a run of rewards on $a^\star$ lifts $p_{a^\star}$ above $1/2$ with probability $\ge(r^\star/\hat x)^n$
-- statement:
--   Consider SAMBA with $\alpha\in(0,1)$ on a Bernoulli bandit with a unique optimal arm. For every $\hat x>0$ there is $n\in\mathbb N$ such that for every initial probability vector with $p_{a^\star}(0)\ge1/\hat x$,
--
--   $$
--   \mathbb P\Big(p_{a^\star}(n)>\tfrac12,\ p_{a^\star}(t)\ge\tfrac1{\hat x}\ \ \forall t\le n\Big)\ge\Big(\frac{r^\star}{\hat x}\Big)^n .
--   $$
--
--   A long enough run in which the optimal arm is played and rewarded lifts its probability above $1/2$ without ever dropping below $1/\hat x$. This gives condition (25a) of Lemma 7 in the proof of Corollary 1.
--
--   **Formalization Note** The number $n$ does not depend on the initial vector, which is how the lemma is used in (25a), an infimum over initial states; the proof gives it.
--
--   Differences from the source:
--
--   - reading: α ∈ (0, 1) is fixed in the algorithm box (p.4), not in the statement → hypotheses 0 < α and α < 1; reason: SAMBA is run with α ∈ (0, 1); for α ≥ 1 the update leaves the simplex (Lemma 10)
--   - reading: If p_{a⋆}(0) ≥ 1/x̂ then there exists n ∈ ℕ → there exists n ≥ 1, the same for every initial vector with p_{a⋆}(0) ≥ 1/x̂; reason: the stronger reading; (25a) of Lemma 7 takes an infimum over initial states, and the proof (p.24) gives it
--   - generalization: x̂ is the constant of Proposition 1 → every x̂ > 0; reason: contains the paper’s x̂
--   - generalization: the arm is drawn with distribution p(t) (p.4) using an independent uniform (p.7) → any jointly measurable rule draw(p, u) with λ{u ∈ [0, 1] : draw(p, u) = a} = p_a on the simplex; reason: every such rule gives the same law of the process; the inverse-CDF rule is one instance
--   - generalization: the leading arm is chosen at random among the maximizers of p(t) (p.7), distribution unspecified → any measurable rule lead(p, v) that returns a maximizer of p, fed by an independent uniform v; reason: the uniform choice among maximizers is one instance
--   - reading: rewards R_a(t) are independent Bernoulli(r_a) (p.6); the policy uses an independent uniform (p.7); ties are broken at random (p.7) → the arm uniforms, tie-break uniforms and rewards over all times are mutually independent; rewards are {0, 1}-valued almost surely; reason: the paper’s independent randomization, made explicit
--   - encoding: a finite set of N arms → a Fintype with at least two elements; reason: for N = 1 the gap ∆ is a maximum over the empty set; only an undefined case is excluded
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, Lemma 6, p.22 (proof §A.2, pp.23–24)

import Mathlib
import Definitions.Def_SambaPG_sambaRun
import Definitions.Def_SambaPG_IsDrawRule
import Definitions.Def_SambaPG_IsLeaderRule

open MeasureTheory

namespace SambaPG

/-- **Lemma 6 (a run of rewards on `a⋆` lifts `p_{a⋆}` above `1/2`).**
Denisov & Walton, arXiv:2007.10229v3, Lemma 6, p.22 (proof §A.2, pp.23–24).

For every `x̂ > 0` there is `n ∈ ℕ` such that, for every initial probability vector with
`p_{a⋆}(0) ≥ 1/x̂`,
`P(p_{a⋆}(n) > 1/2, p_{a⋆}(t) ≥ 1/x̂ ∀ t ≤ n) ≥ (r⋆/x̂)ⁿ`.

**Formalization Note.** `n` depends on `x̂` (and the bandit and `α`) but not on the initial vector:
this uniformity is how Lemma 6 is used in (25a) of Lemma 7 (p.23, infimum over `x₀ ∈ B`), and the
proof on p.24 gives it. `n ∈ ℕ = {1, 2, …}`. Initial vectors range over the closed simplex `𝒫`. The
standing assumption `α ∈ (0, 1)` is a hypothesis; condition (2) is not needed. -/
theorem lemma_6 {A : Type*} [Fintype A] [DecidableEq A] (B : BernoulliBandit A)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (ξ : SambaNoise B μ)
    {draw lead : (A → ℝ) → ℝ → A} (hdraw : IsDrawRule draw) (hlead : IsLeaderRule lead)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ xhat : ℝ, 0 < xhat → ∃ n : ℕ, 0 < n ∧
      ∀ p₀ ∈ stdSimplex ℝ A, 1 / xhat ≤ p₀ B.aStar →
        ENNReal.ofReal ((B.rStar / xhat) ^ n) ≤
          μ {ω | 1 / 2 < sambaRun ξ α draw lead p₀ n ω B.aStar ∧
            ∀ t ≤ n, 1 / xhat ≤ sambaRun ξ α draw lead p₀ t ω B.aStar} := by sorry

end SambaPG
