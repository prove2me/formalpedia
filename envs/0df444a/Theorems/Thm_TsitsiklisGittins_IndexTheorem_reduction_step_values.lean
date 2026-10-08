-- Prove2me | Theorems.Thm_TsitsiklisGittins_IndexTheorem_reduction_step_values
-- name    : TsitsiklisGittins.IndexTheorem.reduction_step_values
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:03.948788+00:00
-- url     : https://prove2.me/theorems/abdc9c5b-4dc7-48db-a19b-bbf3aa3e7d7b
-- title:
--   Reduction step — optimizing within Π(s*) is a bandit problem with one state fewer, the reduced bandit with rate (2.3)
-- statement:
--   Consider the semi-Markov multi-armed bandit problem with finite nonempty state spaces, and let $s^*\in\mathcal X_{i^*}$ have maximal reward rate, $r(s^*)=\max_{x\in\mathcal X}r(x)$. Suppose $\mathcal X_{i^*}$ is not a singleton. Let $\Pi(s^*)$ be the set of policies that give top priority to $s^*$ (they play bandit $i^*$ whenever it is at $s^*$), and let the reduced problem be obtained by reducing bandit $i^*$ by removing $s^*$, with the reduced statistics $\hat\rho,\hat w,\hat D$ and the rate $\hat r$ of (2.3). Then:
--
--   1. the reduced data form a valid bandit problem with discount rate $\beta$, and the number of present states is one less than $|\mathcal X|$;
--   2. for every $\pi\in\Pi(s^*)$ and every joint state $z$ in which bandit $i^*$ is not at $s^*$,
--   $$
--   J_\pi(z)=\hat J_\pi(z),
--   $$
--   where $\hat J$ is the expected discounted reward in the reduced problem;
--   3. every policy of the reduced problem has, on these joint states, the same reduced value as some policy in $\Pi(s^*)$.
--
--   Together, (2) and (3) say that the problem of finding an optimal policy within $\Pi(s^*)$ is the new multi-armed bandit problem, whose state spaces have total cardinality $|\mathcal X|-1$; this is what the induction of Theorem 2.1 is applied to.
--
--   **Formalization Note** A policy of the reduced problem is still a map on all joint states; its choices at joint states with bandit $i^*$ at $s^*$ are irrelevant there, since the reduced data have no transition into $s^*$. The maximality of $r(s^*)$ is the page's setting; the value identity itself does not use it. The reduced problem may contain composite plays that never end (when $s^*$ is absorbing); validity allows this.
-- source:
--   Tsitsiklis, A Short Proof of the Gittins Index Theorem, Ann. Appl. Probab. 4 (1994), p. 197 (PDF p. 4), Section 2, proof of Theorem 2.1, reduction step and equation (2.3)

import Mathlib
import Definitions.Def_TsitsiklisGittins_IndexTheorem_Reduction

namespace TsitsiklisGittins.IndexTheorem

/-- Reduction step in the proof of Theorem 2.1 of Tsitsiklis (1994), p. 197. Let `s = ⟨i*, s*⟩`
have maximal reward rate and let `𝒳_{i*}` not be a singleton. Reducing bandit `i*` by removing
`s*` gives a new multi-armed bandit problem (a valid stage) with one state fewer, and
(a) every policy giving top priority to `s*` has, from every joint state in which bandit `i*` is
not at `s*`, the same expected discounted reward in the original and in the reduced problem;
(b) every policy of the reduced problem has, on those joint states, the value of such a policy. -/
theorem reduction_step_values {n : ℕ} [NeZero n] {X : Fin n → Type} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    [∀ i, Nonempty (X i)] [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (B : SemiMarkovBandit n X)
    (s : Σ i, X i) (hmax : ∀ q : Σ i, X i, B.rate q ≤ B.rate s) (hns : ∃ x : X s.1, x ≠ s.2) :
    (B.initStage.reduce s).Valid B.β ∧
      (B.initStage.reduce s).alive.card + 1 = Fintype.card (Σ i, X i) ∧
      (∀ π : Policy n X, (∀ z : JointState n X, z s.1 = s.2 → π z = s.1) →
        ∀ z : JointState n X, z s.1 ≠ s.2 → B.value π z = (B.initStage.reduce s).value π z) ∧
      (∀ π' : Policy n X, ∃ π : Policy n X, (∀ z : JointState n X, z s.1 = s.2 → π z = s.1) ∧
        ∀ z : JointState n X, z s.1 ≠ s.2 →
          (B.initStage.reduce s).value π z = (B.initStage.reduce s).value π' z) := by sorry

end TsitsiklisGittins.IndexTheorem
