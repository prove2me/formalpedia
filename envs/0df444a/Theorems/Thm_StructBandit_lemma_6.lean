-- Prove2me | Theorems.Thm_StructBandit_lemma_6
-- name    : StructBandit.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:29.19033+00:00
-- url     : https://prove2.me/theorems/4c29ecdc-b115-4f35-a108-402351441973
-- title:
--   Lemma 6 — concentration of $\sum_xN_t(x)I(P_t(x),P(x))$
-- statement:
--   Let $\pi$ be any non-anticipating policy, $t\ge1$ and $\delta\ge|X|(|\mathfrak R|-1)+1$. Then
--
--   $$
--   \mathrm{Prob}\Big[\sum_{x\in X}N_t(x)I(P_t(x),P(x))\ge\delta\Big]\le e\cdot\Big(\frac{\delta\lceil\log(t)\delta+1\rceil2e}{|X|(|\mathfrak R|-1)}\Big)^{|X|(|\mathfrak R|-1)}\cdot\exp(-\delta).
--   $$
--
--   $N_t$ and $P_t$ are counted on the rounds before $t$. This concentration bound for the information distance of arbitrary discrete reward distributions makes the regret of the exploitation phase finite.
--
--   Differences from the source:
--
--   - generalization: stated for DUSA (App. D.1) → every non-anticipating policy whose arm is measurable in the seed (IsAdmissible); reason: the proof (App. E.2) uses only that x_t is F_t-measurable and the rewards form an independent table; DUSA is such a policy
--   - encoding: the base δ⌈log(t)δ+1⌉2e/(|X|(|R|−1)) at |R| = 1 → 0/0 = 0 and 0⁰ = 1, bound e·e^{−δ}; reason: for |R| = 1 every I vanishes and the event is empty; the case is harmless
--   - encoding: terms N_t(x)·I with N_t(x) = 0 and I = +∞ → sum in EReal with 0·⊤ = 0; reason: an unobserved arm contributes nothing
--   - encoding: rewards R_t(x) independent across arms and rounds with law P(·,x) (p.7); expectation over rewards and DUSA's choices (p.28) → BanditEnv: an independent reward table indexed by ℕ × X with μ.real{R_t(x) = r} = P(r,x), and a seed independent of the table; reason: standard table representation of the model; the seed carries DUSA's randomized choices
--   - encoding: P_t, N_t built by Algorithm 1's initialization and recursive update (p.24) → empirical distribution and pull counts of the history of the first t − 1 rounds; reason: the recursion produces exactly the empirical distribution after the point-mass initialization
-- source:
--   Van Parys & Golrezaei, Optimal Learning for Structured Bandits, arXiv:2007.07302v3, Lemma 6, p.52 (proof App. E.2)

import Mathlib
import Definitions.Def_StructBandit_regret
import Definitions.Def_StructBandit_infoDist

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace StructBandit

/-- **Lemma 6 (Concentration Bound for Information Distance).**
Van Parys & Golrezaei, arXiv:2007.07302v3, Lemma 6, p.52 (proof App. E.2).

Let `δ ≥ |X|(|R| − 1) + 1`. Then for any `t ≥ 1`,
`Prob[∑_{x∈X} N_t(x) I(P_t(x), P(x)) ≥ δ] ≤ e · (δ⌈log(t)δ + 1⌉2e / (|X|(|R| − 1)))^{|X|(|R|−1)} · exp(−δ)`.

**Formalization Note.** Stated for every non-anticipating measurable policy (the proof uses only that the
arms are `F_t`-measurable and the rewards form an independent table); DUSA is one such policy. `N_t`,
`P_t` are counted on the history of the first `t − 1` rounds; a term with `N_t(x) = 0` is `0`. The sum is
in `EReal` (`I` may be `+∞`). For `|R| = 1` the base is `0/0`, which Lean evaluates to `0`, and
`0⁰ = 1`; the event is then empty (all `I` vanish), so the case is harmless. -/
theorem lemma_6 {X : Type*} [Fintype X] {R : Finset ℝ} {P : R → X → ℝ} (hP : P ∈ POmega R X)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {V : Type*} [MeasurableSpace V] (E : BanditEnv P μ V) (π : Policy V R X)
    (hπ : IsAdmissible π) (t : ℕ) (ht : 1 ≤ t) (δ : ℝ)
    (hδ : ((Fintype.card X * (R.card - 1) : ℕ) : ℝ) + 1 ≤ δ) :
    μ {ω | ((δ : ℝ) : EReal) ≤ ∑ x, ((pullCount (histAt π E (t - 1) ω) x : ℝ) : EReal) *
        infoDist (fun r => empDist (histAt π E (t - 1) ω) r x) (fun r => P r x)}
      ≤ ENNReal.ofReal (Real.exp 1 *
          (δ * (⌈Real.log t * δ + 1⌉₊ : ℝ) * 2 * Real.exp 1 /
              ((Fintype.card X * (R.card - 1) : ℕ) : ℝ)) ^ (Fintype.card X * (R.card - 1)) *
          Real.exp (-δ)) := by sorry

end StructBandit
