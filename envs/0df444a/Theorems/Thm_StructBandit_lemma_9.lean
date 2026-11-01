-- Prove2me | Theorems.Thm_StructBandit_lemma_9
-- name    : StructBandit.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:33:35.847038+00:00
-- url     : https://prove2.me/theorems/8fcf75c7-9c26-4462-aa99-68802bc348ca
-- title:
--   Lemma 9 — $\mathcal P_u(x^\star_0)$ is open; $\mathrm{Rew}_{\max}$ is continuous (corrected: unique optimal arm at $P$)
-- statement:
--   Let $\mathcal P$ be a structure set and, for an arm $x^\star_0$, let $\mathcal P_u(x^\star_0)$ be the set of $P\in\mathcal P_\Omega$ whose unique optimal arm is $x^\star_0$. Then
--
--   1. $\mathcal P_u(x^\star_0)$ is open (relative to $\mathcal P_\Omega$), and
--   2. for every $P\in\mathrm{int}(\mathcal P)$ **with a unique optimal arm** and every arm $x'\in X$, the map $Q\mapsto\mathrm{Rew}_{\max}(x',Q)$ is continuous at $P$ (within $\mathcal P_\Omega$).
--
--   Near a distribution in $\mathcal P'$ the optimal arm and the classification of the suboptimal arms into deceitful and non-deceitful are therefore stable.
--
--   Differences from the source:
--
--   - correction: (ii) Rewmax(x′,·) is continuous at every P ∈ int(𝒫) → continuous at every P ∈ int(𝒫) with a unique optimal arm; reason: counterexample: R = {0,1}, X = {a,b}, 𝒫 = P_Ω, P(1,a) = P(1,b) = 1/2 (interior); Rewmax(a,P) = 1/2, but Qₙ(1,a) = 1/2, Qₙ(1,b) = 1/2 + 1/n → P has x⋆(Qₙ) = {b} and Rewmax(a,Qₙ) = 1; the proof treats P ∈ P_u(x⋆₀) (p.70), the case in which the lemma is used
--   - encoding: 'P_u(x⋆₀) is an open set', 'continuous function at P' → P_u(x⋆₀) = U ∩ P_Ω for an open U; ContinuousWithinAt on P_Ω into EReal; reason: P_u(x⋆₀) ⊆ P_Ω carries the subspace topology; Rewmax may be infinite off 𝒫
--   - encoding: I, Dist, C, C̄, Rewmax, Dual, Dual‾ as extended-real optimal values ('max' over ρ ≥ 0 in (17) and 'max' in (8) included); SU := +∞ if (19) is infeasible → EReal values with inf ∅ = +∞, sup ∅ = −∞; SU returns Option (none = +∞), and none also when (19) is feasible but has no minimizer; reason: the source's conventions; a supremum need not be attained off the source's setting; (19) is an argmin, so nothing is defined without a minimizer; Lean's log 0 = 0 and x/0 = 0 decide no case
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Lemma 9, p.54 (proof App. F, p.70)

import Mathlib
import Definitions.Def_StructBandit_PPrime

open scoped BigOperators

namespace StructBandit

/-- **Lemma 9 (Stability of the Optimal Arm and Continuity of the Maximal Reward)**, with part (ii)
corrected. Van Parys & Golrezaei, arXiv:2007.07302v3, Lemma 9, p.54 (proof App. F, p.70).

Let `P_u(x⋆₀)` be the set of reward distributions `P ∈ P_Ω` with the unique optimal arm `x⋆₀`. Then
(i) `P_u(x⋆₀)` is open (relative to `P_Ω`), and
(ii) for every `P ∈ int(𝒫)` **with a unique optimal arm** and every arm `x′ ∈ X`, the maximum reward
`Q ↦ Rewmax(x′,Q)` is continuous at `P` (within `P_Ω`).

**Formalization Note.** Printed (ii) asserts continuity at every `P ∈ int(𝒫)`, which fails when `P` has
two optimal arms (two Bernoulli arms with equal means `1/2`, `𝒫 = P_Ω`: `Rewmax(a,P) = 1/2`, but raising the
other arm's mean by `1/n` gives `Rewmax(a,Qₙ) = 1`). The proof treats `P ∈ P_u(x⋆₀)` (p.70), the case in
which the lemma is used (`P ∈ 𝒫′`). -/
theorem lemma_9 {X : Type*} [Fintype X] [Nonempty X] {R : Finset ℝ} {S : Set (R → X → ℝ)}
    (hS : IsStructureSet S) :
    (∀ x₀ : X, ∃ U : Set (R → X → ℝ), IsOpen U ∧
        {Q | Q ∈ POmega R X ∧ optArms Q = {x₀}} = U ∩ POmega R X) ∧
    (∀ P ∈ relInt S, ∀ x₀ : X, optArms P = {x₀} → ∀ x' : X,
        ContinuousWithinAt (fun Q => rewMax S x' Q) (POmega R X) P) := by sorry

end StructBandit
