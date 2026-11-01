-- Prove2me | Theorems.Thm_StructBandit_lemma_5
-- name    : StructBandit.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:33:52.309862+00:00
-- url     : https://prove2.me/theorems/9f160e95-bb6d-4dde-80c6-bb648650557e
-- title:
--   Lemma 5 — concentration of $P_{t(s,x)}(r,x)$ at a stopping time
-- statement:
--   Let $\pi$ be any non-anticipating policy, $x\in X$ an arm, $r\in\mathfrak R$, $T\ge0$, $s\ge1$, $\phi(s)\in\mathbb R$ and $\kappa>0$. Let $t(s,x)\in\{s,\dots,T+1\}$ be a stopping time such that either $N_{t(s,x)}(x)\ge\phi(s)$ or $t(s,x)=T+1$. Then
--
--   $$
--   \mathrm{Prob}\big[|P_{t(s,x)}(r,x)-P(r,x)|\ge\kappa,\ t(s,x)\le T\big]\le 2\exp(-2\phi(s)\kappa^2).
--   $$
--
--   Here $N_t(x)$ and $P_t$ are the pull count and the empirical distribution of the rounds before $t$. This Hoeffding-type bound at a random time controls the bad events in both phases of DUSA.
--
--   Differences from the source:
--
--   - generalization: stated for DUSA (App. D.1) → every non-anticipating policy whose arm is measurable in the seed (IsAdmissible); reason: the proof (App. E) uses only that x_t is F_t-measurable and the rewards form an independent table; DUSA is such a policy
--   - reading: 'N_τ(x) is the number of rounds within the first τ rounds that arm x is played' → N_t(x) and P_t are counted on the history of the rounds before t, the stopping property is {t(s,x) = n} ∈ σ(seed, first n − 1 rounds); reason: this is Algorithm 1's N_t, P_t (N_{|X|+1} = 1); P_t is the mean of N_t(x) observations only with this convention
--   - reading: κ unqualified in Lemma 5 → 0 < κ; reason: κ is the positive threshold of the bad events (p.53); for κ ≤ 0 the event is {t(s,x) ≤ T} and the bound can fail
--   - encoding: rounds t ∈ [T] and s → 1 ≤ s; reason: rounds start at 1
--   - encoding: rewards R_t(x) independent across arms and rounds with law P(·,x) (p.7); expectation over rewards and DUSA's choices (p.28) → BanditEnv: an independent reward table indexed by ℕ × X with μ.real{R_t(x) = r} = P(r,x), and a seed independent of the table; reason: standard table representation of the model; the seed carries DUSA's randomized choices
--   - encoding: P_t, N_t built by Algorithm 1's initialization and recursive update (p.24) → empirical distribution and pull counts of the history of the first t − 1 rounds; reason: the recursion produces exactly the empirical distribution after the point-mass initialization
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Lemma 5, p.52 (proof App. E.1)

import Mathlib
import Definitions.Def_StructBandit_regret

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace StructBandit

/-- **Lemma 5 (Concentration Bound).**
Van Parys & Golrezaei, arXiv:2007.07302v3, Lemma 5, p.52 (proof App. E.1).

For any arm `x`, let `t(s,x) ∈ {s, …, T+1}` be a stopping time such that either `N_{t(s,x)}(x) ≥ φ(s)` or
`t(s,x) = T + 1`. Then for every `r ∈ R` and `κ > 0`,
`Prob[|P_{t(s,x)}(r,x) − P(r,x)| ≥ κ, t(s,x) ≤ T] ≤ 2 exp(−2φ(s)κ²)`.

**Formalization Note.** Stated for every non-anticipating measurable policy `π` (the proof uses only that
`x_t` is `F_t`-measurable and that the rewards form an independent table); DUSA is one such policy.
Round `n` sees the history of `n − 1` rounds, and the stopping property is `{t(s,x) = n} ∈ F_n =
σ(seed, first n − 1 rounds)`. `N_n(x)` and `P_n` are counted on that history, as in Algorithm 1. -/
theorem lemma_5 {X : Type*} [Fintype X] {R : Finset ℝ} {P : R → X → ℝ} (hP : P ∈ POmega R X)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V : Type*} [MeasurableSpace V] (E : BanditEnv P μ V) (π : Policy V R X)
    (hπ : IsAdmissible π) (x : X) (r : R) (T s : ℕ) (hs : 1 ≤ s) (φ κ : ℝ) (hκ : 0 < κ)
    (τ : Ω → ℕ) (hτ_range : ∀ ω, s ≤ τ ω ∧ τ ω ≤ T + 1)
    (hτ_stop : ∀ n, MeasurableSet[histSigma π E (n - 1)] {ω | τ ω = n})
    (hτ_count : ∀ ω, φ ≤ (pullCount (histAt π E (τ ω - 1) ω) x : ℝ) ∨ τ ω = T + 1) :
    μ {ω | κ ≤ |empDist (histAt π E (τ ω - 1) ω) r x - P r x| ∧ τ ω ≤ T}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * φ * κ ^ 2)) := by sorry

end StructBandit
