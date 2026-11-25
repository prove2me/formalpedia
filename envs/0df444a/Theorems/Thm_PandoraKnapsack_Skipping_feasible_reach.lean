-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_feasible_reach
-- name    : PandoraKnapsack.Skipping.feasible_reach
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T17:13:27.748429+00:00
-- url     : https://prove2.me/theorems/4a00b1b4-2b1c-551e-bc90-6d232367c564
-- title:
--   Algorithm 1 reaches assigned times for any feasible LP input
-- statement:
--   Let $I$ be a valid instance and run Algorithm 1 with any feasible solution $x$ of the time-indexed LP at capacity $T$. If $A$ is the event that item $i$ is assigned choice $j$ and start $t$, and $L$ is its predecessor load, then
--   $$
--   \Pr(A\cap\{L\le t\})\ge \tfrac12\Pr(A).
--   $$
--
--   This extends Lemma 5.3 to approximate and sparse feasible solutions, including zero-probability assignments and $t=0$.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora's Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, Lemma 5.3. Generalization replacing optimality by feasibility, the only property used in the reach bound.

import Definitions.Def_PandoraKnapsack_Skipping_Algorithm1

namespace PandoraKnapsack.Skipping

theorem feasible_reach {n m T : ℕ} (I : Instance n m T) (hI : IsValid I) (xStar : LPArray n m)
    (hx : PsiFeasible I T xStar) (i : Fin n) (j : Fin m) (t : Fin (T + 1)) :
    (1 / 2 : ℝ) * alg1Prob I xStar (fun ω => ω.1 i = some (j, t)) ≤
      alg1Prob I xStar (fun ω => ω.1 i = some (j, t) ∧ predecessorLoad ω i ≤ (t : ℕ)) := by sorry

end PandoraKnapsack.Skipping
