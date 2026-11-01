-- Prove2me | Theorems.Thm_SambaPG_proposition_1
-- name    : SambaPG.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:39:39.737296+00:00
-- url     : https://prove2.me/theorems/b4fec893-e60c-4447-bb02-2495d4199c49
-- title:
--   Proposition 1 — finite expected return time $\tau(\hat x)$ from $E(\hat x)$ under (2)
-- statement:
--   Consider SAMBA with $\alpha\in(0,1)$ on a Bernoulli bandit with a unique optimal arm, and assume condition (2), $\alpha<\Delta/(r^\star-\Delta)$. For $\hat x>0$ let
--
--   $$
--   \tau(\hat x):=\min\{t\ge1:p_{a^\star}(t)>1/\hat x\},\qquad E(\hat x):=\{p\in\mathcal P:(1-\alpha)/\hat x\le p_{a^\star}<1/\hat x\},
--   $$
--
--   where $\mathcal P$ is the set of probability vectors on the arms. Then there is a constant $\hat x>N$ such that
--
--   $$
--   \sup_{p\in E(\hat x)}\mathbb E\big[\tau(\hat x)\,\big|\,p(0)=p\big]<\infty .
--   $$
--
--   The optimal arm's probability does not stay small for long: from just below $1/\hat x$, it returns above $1/\hat x$ in finite expected time, uniformly in the starting point.
--
--   **Formalization Note** $\mathbb E[\tau(\hat x)\mid p(0)=p]$ is the expectation of the hitting time for the SAMBA run started at $p$. The hitting time takes values in $\mathbb N\cup\{\infty\}$.
--
--   Differences from the source:
--
--   - reading: α ∈ (0, 1) is fixed in the algorithm box (p.4), not in the statement → hypotheses 0 < α and α < 1; reason: SAMBA is run with α ∈ (0, 1); for α ≥ 1 the update leaves the simplex (Lemma 10)
--   - generalization: α < ∆/(r⋆ − ∆), condition (2) → α (r⋆ − ∆) < ∆; reason: equivalent to (2) when r⋆ > ∆; also covers r⋆ = ∆, where the printed fraction is undefined
--   - generalization: there exists a positive constant x̂ → there exists x̂ > N; reason: stronger, implies x̂ > 0; the proof chooses x̂ > N (p.8)
--   - encoding: sup over initial states of E[τ | p(0) = p] < ∞ → an ℕ∞-valued hitting time, the lintegral of the run started at p, bounded by one finite M for all such p; reason: a time that is infinite with positive probability has expectation ∞, never a junk 0
--   - generalization: the arm is drawn with distribution p(t) (p.4) using an independent uniform (p.7) → any jointly measurable rule draw(p, u) with λ{u ∈ [0, 1] : draw(p, u) = a} = p_a on the simplex; reason: every such rule gives the same law of the process; the inverse-CDF rule is one instance
--   - generalization: the leading arm is chosen at random among the maximizers of p(t) (p.7), distribution unspecified → any measurable rule lead(p, v) that returns a maximizer of p, fed by an independent uniform v; reason: the uniform choice among maximizers is one instance
--   - reading: rewards R_a(t) are independent Bernoulli(r_a) (p.6); the policy uses an independent uniform (p.7); ties are broken at random (p.7) → the arm uniforms, tie-break uniforms and rewards over all times are mutually independent; rewards are {0, 1}-valued almost surely; reason: the paper’s independent randomization, made explicit
--   - encoding: a finite set of N arms → a Fintype with at least two elements; reason: for N = 1 the gap ∆ is a maximum over the empty set; only an undefined case is excluded
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, Proposition 1, p.8, with (8), p.8

import Mathlib
import Definitions.Def_SambaPG_sambaRun
import Definitions.Def_SambaPG_IsDrawRule
import Definitions.Def_SambaPG_IsLeaderRule
import Definitions.Def_SambaPG_firstHitFrom

open MeasureTheory
open scoped ENNReal

namespace SambaPG

/-- **Proposition 1 (finite expected return time above `1/x̂`).**
Denisov & Walton, arXiv:2007.10229v3, Proposition 1, p.8, with (8), p.8.

Let `τ(x̂) := min{t ≥ 1 : p_{a⋆}(t) > 1/x̂}` and `E(x̂) := {p ∈ 𝒫 : (1 − α)/x̂ ≤ p_{a⋆} < 1/x̂}`, where
`𝒫` is the set of probability vectors on the arms (§3.5, p.7). If condition (2),
`α < ∆/(r⋆ − ∆)`, holds, there is a constant `x̂ > N` such that
`sup_{p ∈ E(x̂)} E[τ(x̂) | p(0) = p] < ∞`.

**Formalization Note.** `E[τ(x̂) | p(0) = p]` is the expectation of the hitting time for the SAMBA
run started at `p`; `τ(x̂)` is `ℕ∞`-valued and the expectation is a `lintegral`, so a time that is
infinite with positive probability has expectation `∞`. Condition (2) is written
`α (r⋆ − ∆) < ∆`. The algorithm's standing assumption `α ∈ (0, 1)` is a hypothesis. The draw rule
and the tie-breaking rule are arbitrary (`IsDrawRule`, `IsLeaderRule`). -/
theorem proposition_1 {A : Type*} [Fintype A] [DecidableEq A] (B : BernoulliBandit A)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (ξ : SambaNoise B μ)
    {draw lead : (A → ℝ) → ℝ → A} (hdraw : IsDrawRule draw) (hlead : IsLeaderRule lead)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (h2 : α * (B.rStar - B.gap) < B.gap) :
    ∃ xhat : ℝ, (Fintype.card A : ℝ) < xhat ∧ ∃ M : ℝ≥0∞, M < ⊤ ∧
      ∀ p₀ ∈ stdSimplex ℝ A, (1 - α) / xhat ≤ p₀ B.aStar → p₀ B.aStar < 1 / xhat →
        ∫⁻ ω, ((firstHitFrom
            (fun t => 1 / xhat < sambaRun ξ α draw lead p₀ t ω B.aStar) 1 : ℕ∞) : ℝ≥0∞) ∂μ
          ≤ M := by sorry

end SambaPG
