-- Prove2me | Theorems.Thm_StableFA_Discounted_Supplement_theorem_A_1
-- name    : StableFA.Discounted.Supplement.theorem_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T10:41:01.348812+00:00
-- url     : https://prove2.me/theorems/24c1f794-5334-4ea1-a4a7-cf8ac1368a45
-- title:
--   Theorem A.1 — derived MDP for Q-learning
-- statement:
--   Let $M$ be a finite Markov decision process with non-goal states $x$, nonempty finite action sets $U(x)$, expected costs $c_{xa}$ and transition probabilities $p_{xay}$. The missing row mass is transition to a cost-free absorbing goal with zero Q-value. For any real $\gamma$, define the parallel Q-learning backup by
--   $$
--   (T_M Q)(x,a)=c_{xa}+\gamma\sum_y p_{xay}\min_{b\in U(y)}Q(y,b).
--   $$
--   Let $A$ be an averager on admissible state–action pairs, with constants $k_{zc}$, nonnegative constant weights $\beta_{zc}$, goal weights $\beta^g_{zc}$ and target weights $\beta_{zcxa}$ satisfying
--   $$\beta_{zc}+\beta^g_{zc}+\sum_x\sum_{a\in U(x)}\beta_{zcxa}=1.$$
--   Its mapping is $(M_AQ)(z,c)=\beta_{zc}k_{zc}+\sum_x\sum_{a\in U(x)}\beta_{zcxa}Q(x,a)$. Define $M'$ to have the same states and admissible actions, with
--   $$c'_{zc}=\sum_x\sum_{a\in U(x)}\beta_{zcxa}c_{xa}+\beta_{zc}k_{zc},\qquad p'_{zcy}=\sum_x\sum_{a\in U(x)}\beta_{zcxa}p_{xay}.$$
--   The transition deficit goes to the goal. Then, as operators on every Q-function,
--   $$M_A\circ T_M=T_{M'}.$$
--   This includes discounted and nondiscounted backups and gives the explicit derived process of Appendix A. It asserts the operator identity, with no convergence claim.
--
--   **Formalization Note** Target coordinates are admissible pairs, represented by a subtype. Q-functions and output coordinates are stored on all state–action pairs; values at inadmissible input pairs are ignored by both the averager and the next-state minimum. The output equality also holds on these unused coordinates. `DecidableEq C` supplies finite-set membership and imposes no mathematical restriction. The minimum is `Finset.inf'` on a nonempty action set; no real infimum default occurs. The initial distribution never enters either operator.
--
--   Differences from the source:
--   - encoding: State 1 is an absorbing, cost-free goal and has zero continuation value → The goal is the implicit termination state of BertsekasSSPModel; a separate nonnegative goal weight multiplies zero; reason: Appendix A, p. 19, sends the transition deficit to state 1 with V(1) ≡ 0; this is the convention of the published missions
--   - generalization: A single finite action space A → Finite nonempty state-dependent admissible sets U(x); target weights are indexed only by admissible pairs; reason: The same finite sums and minimum over the next state’s actions apply; U(x) = A recovers every original instance
--   - generalization: Discount γ ∈ [0,1], including γ = 1 → Every real γ; reason: The Appendix A identity is finite algebra and the constructed model is independent of γ; no step requires a bound on γ
--   - generalization: §2 assumes that M has a well-defined optimal value function → No optimal-value existence hypothesis; reason: No optimal value occurs in the operator identity; the sorry-free verification proves it for all finite real costs and substochastic transitions
-- source:
--   Gordon, Stable Function Approximation in Dynamic Programming, Tech. Rep. CMU-CS-95-103, Carnegie Mellon University (1995), p. 19 (PDF p. 21), Theorem A.1 (Derived MDP for Q-learning), full statement and proof

import Mathlib
import Definitions.Def_BertsekasSSPModel
import Definitions.Def_StableFA_Discounted_Supplement_QBackup
import Definitions.Def_StableFA_Discounted_Supplement_PairAverager

namespace StableFA.Discounted.Supplement

/-- Theorem A.1: backing up and then fitting is the Q-backup of the explicit derived MDP. -/
theorem theorem_A_1 {n : ℕ} {C : Type} [Fintype C] [DecidableEq C]
    (M : BertsekasSSPModel n C) (A : PairAverager M) (γ : ℝ) :
    A.apply ∘ qBackup M γ = qBackup (derivedModel M A) γ := by sorry

end StableFA.Discounted.Supplement
