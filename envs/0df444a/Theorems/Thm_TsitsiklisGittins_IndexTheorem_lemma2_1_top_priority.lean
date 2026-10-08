-- Prove2me | Theorems.Thm_TsitsiklisGittins_IndexTheorem_lemma2_1_top_priority
-- name    : TsitsiklisGittins.IndexTheorem.lemma2_1_top_priority
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:30.058847+00:00
-- url     : https://prove2.me/theorems/2d4e2fcd-742c-491b-ad07-6fa1a6e1d88e
-- title:
--   Lemma 2.1 — some optimal policy always plays bandit i* when it is at a state s* of maximal reward rate
-- statement:
--   Consider the semi-Markov multi-armed bandit problem with $n\ge1$ bandits, finite nonempty state spaces $\mathcal X_1,\dots,\mathcal X_n$ and discount rate $\beta>0$. Let $s^*\in\mathcal X$ satisfy
--   $$
--   r(s^*)=\max_{x\in\mathcal X}r(x),
--   $$
--   where $r$ is the reward rate (2.1), and let $i^*$ be such that $s^*\in\mathcal X_{i^*}$. Then there exists an optimal policy $\pi$ that obeys the following rule: whenever bandit $i^*$ is at state $s^*$, bandit $i^*$ is played.
--
--   The lemma says that a state of maximal reward rate can be given top priority; it is the first step of the induction proving Theorem 2.1.
--
--   **Formalization Note** Optimality is over the paper's class of stationary deterministic policies and for every initial joint state; the existence of an optimal policy is part of the conclusion, not a hypothesis. Bandits are indexed by `Fin n`.
-- source:
--   Tsitsiklis, A Short Proof of the Gittins Index Theorem, Ann. Appl. Probab. 4 (1994), p. 196 (PDF p. 3), Lemma 2.1

import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_SemiMarkovBandit

namespace TsitsiklisGittins.IndexTheorem

/-- Lemma 2.1 of Tsitsiklis (1994), p. 196: if `s = ⟨i*, s*⟩` has maximal reward rate (2.1),
`r(s*) = max_{x ∈ 𝒳} r(x)`, then there exists an optimal policy that plays bandit `i*` whenever
bandit `i*` is at state `s*`. -/
theorem lemma2_1_top_priority {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (s : Σ i, X i) (hmax : ∀ q : Σ i, X i, B.rate q ≤ B.rate s) :
    ∃ π : Policy n X, B.IsOptimal π ∧ ∀ z : JointState n X, z s.1 = s.2 → π z = s.1 := by sorry

end TsitsiklisGittins.IndexTheorem
