-- Prove2me | Theorems.Thm_WeberGittins_Submodular_value_concave_increasing_identical
-- name    : WeberGittins.Submodular.value_concave_increasing_identical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:55:41.743585+00:00
-- url     : https://prove2.me/theorems/a419e1c2-bd10-45de-b1b4-ebf2db3ffb3e
-- title:
--   Section 5, p. 1030 — for identical bandits in the same initial state, $V(S)$ is concave and increasing in $n$
-- statement:
--   Suppose all bandits are statistically the same (one state space $S$, standard Borel, one transition kernel $P$, one measurable reward $r$, rewards nonnegative and uniformly bounded, $0<\beta<1$) and all start in the same state $y$. Let $v(m)$ be the maximal expected total-discounted reward of the problem with $m$ such bandits ($v(0)=0$). Then $v$ is nondecreasing and concave:
--   $$
--   v(m)\le v(m+1),\qquad v(m+2)-v(m+1)\le v(m+1)-v(m)\qquad(m\ge0).
--   $$
--
--   Weber derives this from Theorem 4 with $I=\{1,\dots,n-1\}$ and $J=\{2,\dots,n\}$: each additional identical bandit adds no more value than the previous one.
--
--   **Formalization Note** $v(m)$ is `restrictedValue P r β (fun _ : Fin m => y) Finset.univ`. "Increasing" is read as nondecreasing (`Monotone`): adding a bandit can leave the value unchanged, for instance when all rewards are $0$. "Statistically the same" is automatic in the common-kernel model once the initial states coincide. The statement includes $m=0$, where $v(0)=V(\emptyset)=0$.
-- source:
--   Weber, On the Gittins index for multiarmed bandits, Ann. Appl. Probab. 2 (1992), p. 1030, Section 5 ("If all bandits are statistically the same and initially in the same state, then a consequence of (9) is that V(S) is a concave increasing function of n")

import Definitions.Def_WeberGittins_Submodular_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace WeberGittins.Submodular

/-- Weber (1992), Section 5, p. 1030: if all bandits are statistically the same (one kernel `P`,
one reward `r`) and initially in the same state `y`, then `V(S)`, as a function of the number `m`
of bandits, is (weakly) increasing and concave: `v (m + 2) − v (m + 1) ≤ v (m + 1) − v m`. -/
theorem value_concave_increasing_identical {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ} (hr : Measurable r)
    (hrb : WeberGittins.Suboptimality.RewardsNonnegBounded r) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (y : S) :
    let v : ℕ → ℝ := fun m => restrictedValue P r β (fun _ : Fin m => y) Finset.univ
    Monotone v ∧ ∀ m : ℕ, v (m + 2) - v (m + 1) ≤ v (m + 1) - v m := by sorry

end WeberGittins.Submodular
