-- Prove2me | Theorems.Thm_WeberGittins_Submodular_theorem4_value_submodular
-- name    : WeberGittins.Submodular.theorem4_value_submodular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:31.624109+00:00
-- url     : https://prove2.me/theorems/b0bbb3d2-401a-4b00-9fd3-4ce5881bee14
-- title:
--   Theorem 4 — $V(I\cap J)+V(I\cup J)\le V(I)+V(J)$: the optimal value is submodular in the set of bandits
-- statement:
--   Consider $n$ bandits on a standard Borel state space $S$, each a Markov chain with transition kernel $P$ that moves only when played, with measurable reward $r$; rewards are nonnegative and uniformly bounded, and $0<\beta<1$. Fix the initial states $x(0)=x$. For a set $I\subseteq\{1,\dots,n\}$ of bandits, let $V(I)$ be the maximal expected total-discounted reward of the problem $P(I)$ restricted to the bandits in $I$ (with $V(\emptyset)=0$). Then for any $I,J\subseteq\{1,\dots,n\}$,
--   $$
--   V(I\cap J)+V(I\cup J)\le V(I)+V(J).
--   $$
--
--   That is, $V$ is a submodular set function of the available bandits: the gain from adding a bandit to a set of available bandits does not increase as the set grows. This is the new result of Weber's paper. With $I$, $J$ disjoint it gives subadditivity $V(I\cup J)\le V(I)+V(J)$, and it implies the concavity in $n$ of the value for identical bandits and Tsitsiklis's bound for a retirement option.
--
--   **Formalization Note** $V(I)$ is `restrictedValue P r β x I`: the supremum of the published discounted value over all policies of the $|I|$-armed game whose arms are the bandits of $I$, in increasing order, started at their states in $x$; $V(\emptyset)=0$ explicitly. One kernel and one reward on one state space encode bandits with different dynamics (disjoint union of the state spaces). The paper's hypotheses "rewards are nonnegative and uniformly bounded" and $0<\beta<1$ (Section 1, p. 1024) are binders; `StandardBorelSpace S` and `Measurable r` are regularity assumptions of the published model that the paper leaves implicit. No hypothesis makes the bandits identical.
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1030, Theorem 4, eq. (9)

import Definitions.Def_WeberGittins_Submodular_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WeberGittins.Submodular

/-- Weber (1992), Theorem 4, eq. (9), p. 1030: the maximal expected total-discounted reward is a
submodular function of the set of available bandits: for any `I, J ⊆ {1, …, n}`,
`V(I ∩ J) + V(I ∪ J) ≤ V(I) + V(J)`. Standing assumptions of Section 1 (p. 1024): rewards
nonnegative and uniformly bounded, `0 < β < 1`. -/
theorem theorem4_value_submodular {n : ℕ} {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (x : Fin n → S)
    (I J : Finset (Fin n)) :
    restrictedValue P r β x (I ∩ J) + restrictedValue P r β x (I ∪ J) ≤
      restrictedValue P r β x I + restrictedValue P r β x J := by sorry

end WeberGittins.Submodular
