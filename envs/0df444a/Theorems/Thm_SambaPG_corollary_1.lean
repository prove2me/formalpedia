-- Prove2me | Theorems.Thm_SambaPG_corollary_1
-- name    : SambaPG.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:39:40.009412+00:00
-- url     : https://prove2.me/theorems/05d06335-64bc-487e-a369-54547e4ceb50
-- title:
--   Corollary 1 — finite expected return time $\tau(2)$ from $E(2)$ under (2)
-- statement:
--   Consider SAMBA with $\alpha\in(0,1)$ on a Bernoulli bandit with a unique optimal arm, under condition (2). Let $\tau(2)=\min\{t\ge1:p_{a^\star}(t)>1/2\}$ and $E(2)=\{p\in\mathcal P:(1-\alpha)/2\le p_{a^\star}<1/2\}$. Then
--
--   $$
--   \sup_{p\in E(2)}\mathbb E\big[\tau(2)\,\big|\,p(0)=p\big]<\infty .
--   $$
--
--   Once the optimal arm drops just below probability $1/2$, it becomes the leading arm again in finite expected time, uniformly in the starting point. The paper cites this result as "Corollary 4".
--
--   **Formalization Note** The printed statement opens with "there exists a positive constant $\hat x$", which plays no role ($E(2)$ and $\tau(2)$ do not involve $\hat x$) and is dropped.
--
--   Differences from the source:
--
--   - reading: α ∈ (0, 1) is fixed in the algorithm box (p.4), not in the statement → hypotheses 0 < α and α < 1; reason: SAMBA is run with α ∈ (0, 1); for α ≥ 1 the update leaves the simplex (Lemma 10)
--   - generalization: α < ∆/(r⋆ − ∆), condition (2) → α (r⋆ − ∆) < ∆; reason: equivalent to (2) when r⋆ > ∆; also covers r⋆ = ∆, where the printed fraction is undefined
--   - encoding: there exists a positive constant x̂ such that … → the quantifier is dropped; reason: x̂ does not occur in the conclusion
--   - encoding: sup over initial states of E[τ | p(0) = p] < ∞ → an ℕ∞-valued hitting time, the lintegral of the run started at p, bounded by one finite M for all such p; reason: a time that is infinite with positive probability has expectation ∞, never a junk 0
--   - generalization: the arm is drawn with distribution p(t) (p.4) using an independent uniform (p.7) → any jointly measurable rule draw(p, u) with λ{u ∈ [0, 1] : draw(p, u) = a} = p_a on the simplex; reason: every such rule gives the same law of the process; the inverse-CDF rule is one instance
--   - generalization: the leading arm is chosen at random among the maximizers of p(t) (p.7), distribution unspecified → any measurable rule lead(p, v) that returns a maximizer of p, fed by an independent uniform v; reason: the uniform choice among maximizers is one instance
--   - reading: rewards R_a(t) are independent Bernoulli(r_a) (p.6); the policy uses an independent uniform (p.7); ties are broken at random (p.7) → the arm uniforms, tie-break uniforms and rewards over all times are mutually independent; rewards are {0, 1}-valued almost surely; reason: the paper’s independent randomization, made explicit
--   - encoding: a finite set of N arms → a Fintype with at least two elements; reason: for N = 1 the gap ∆ is a maximum over the empty set; only an undefined case is excluded
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, Corollary 1, p.9 (cited as Corollary 4 on pp.8, 9, 11, 12; proof §A.1, pp.22–23)

import Mathlib
import Definitions.Def_SambaPG_sambaRun
import Definitions.Def_SambaPG_IsDrawRule
import Definitions.Def_SambaPG_IsLeaderRule
import Definitions.Def_SambaPG_firstHitFrom

open MeasureTheory
open scoped ENNReal

namespace SambaPG

/-- **Corollary 1 (finite expected return time above `1/2`).**
Denisov & Walton, arXiv:2007.10229v3, Corollary 1, p.9 (cited as "Corollary 4" on pp.8, 9, 11, 12
and proved in §A.1, pp.22–23).

If condition (2) holds, then `sup_{p ∈ E(2)} E[τ(2) | p(0) = p] < ∞`, where
`τ(2) = min{t ≥ 1 : p_{a⋆}(t) > 1/2}` and `E(2) = {p ∈ 𝒫 : (1 − α)/2 ≤ p_{a⋆} < 1/2}` (eq. (8) with
`x̂ = 2`).

**Formalization Note.** The printed "there exists a positive constant `x̂`" is vestigial: neither
`E(2)` nor `τ(2)` involves `x̂`, so it is dropped. Condition (2) is written `α (r⋆ − ∆) < ∆`; the
standing assumption `α ∈ (0, 1)` is a hypothesis. Hitting times are `ℕ∞`-valued, expectations are
`lintegral`s. -/
theorem corollary_1 {A : Type*} [Fintype A] [DecidableEq A] (B : BernoulliBandit A)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (ξ : SambaNoise B μ)
    {draw lead : (A → ℝ) → ℝ → A} (hdraw : IsDrawRule draw) (hlead : IsLeaderRule lead)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (h2 : α * (B.rStar - B.gap) < B.gap) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧
      ∀ p₀ ∈ stdSimplex ℝ A, (1 - α) / 2 ≤ p₀ B.aStar → p₀ B.aStar < 1 / 2 →
        ∫⁻ ω, ((firstHitFrom
            (fun t => 1 / 2 < sambaRun ξ α draw lead p₀ t ω B.aStar) 1 : ℕ∞) : ℝ≥0∞) ∂μ
          ≤ M := by sorry

end SambaPG
