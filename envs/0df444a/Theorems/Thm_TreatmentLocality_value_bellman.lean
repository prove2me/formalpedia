-- Prove2me | Theorems.Thm_TreatmentLocality_value_bellman
-- name    : TreatmentLocality.value_bellman
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T02:54:16.521824+00:00
-- url     : https://prove2.me/theorems/b991e48f-2a44-4fba-848a-107e3edc604a
-- title:
--   The Bellman equation $V^a = r^a + \gamma P^a V^a$
-- statement:
--   **The Bellman equation for the policy value.** With $P^a$ the transition matrix and $r^a$ the mean-reward vector of the policy that plays arm $a$ in the SST model, the discounted value function $V^a = (I - \gamma P^a)^{-1} r^a$ satisfies
--   $$V^a \;=\; r^a + \gamma P^a V^a, \qquad\text{i.e.}\qquad V^a(s) = r^a(s) + \gamma \sum_{j} P^a(s,j)\, V^a(j) .$$
--
--   This is the fixed-point identity behind every temporal-difference argument: it says precisely that the residual $r + \gamma V^a(s') - V^a(s)$ has conditional mean zero given the current state $s$, when $r$ and $s'$ are drawn from the true reward and transition laws at $(s, a)$. It is the ingredient that turns the linearisation of a model-based estimator into a centred statistic (arXiv:2407.19618, §2).
-- source:
--   H. Chen, D. Simchi-Levi, C. Wang, Improving the Estimation of Lifetime Effects in A/B Testing via Treatment Locality, arXiv:2407.19618v3, §2, eq. (2) (the discounted value function V^a = (I - gamma P^a)^{-1} r^a of the SST model). See also M. L. Puterman, Markov Decision Processes, Wiley 1994, Theorem 6.1.1.

import Definitions.Def_TreatmentLocality

open MeasureTheory ProbabilityTheory TreatmentLocality
open scoped NNReal ENNReal

theorem TreatmentLocality.value_bellman {S : Type*} [DecidableEq S] [Fintype S]
    (M : Model S) (a : Bool) :
    M.value a = M.polReward a + M.γdisc • (M.polTrans a).mulVec (M.value a) := by sorry
