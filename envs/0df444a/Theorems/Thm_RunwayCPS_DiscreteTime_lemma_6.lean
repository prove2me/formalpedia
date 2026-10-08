-- Prove2me | Theorems.Thm_RunwayCPS_DiscreteTime_lemma_6
-- name    : RunwayCPS.DiscreteTime.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:52.909201+00:00
-- url     : https://prove2.me/theorems/e2f49e95-2777-401f-8cba-b1a199b86055
-- title:
--   Lemma 6 — every feasible schedule, in particular an optimal one, is represented by a source-sink path of the modified network
-- statement:
--   Assume $k\ge 1$. Let $(\sigma,t)$ be a feasible schedule, where the separations may violate the triangle inequality. Then the discrete-time triangle-inequality modified network has a source-sink path $(i_1,t_1,d_1),\dots,(i_n,t_n,d_n)$ that represents it:
--   $$
--   \mathrm{fin}(i_p)=\sigma(p)\quad\text{and}\quad t_p \text{ is the landing time of position } p,\qquad p=1,\dots,n .
--   $$
--
--   The paper states this for an optimal schedule (minimizing a sum of positive separable costs); here it is stated for every feasible schedule, which contains the paper's statement. Together with Lemma 5 it shows that the paths of the network are exactly the feasible schedules.
--
--   **Formalization Note** Since $\Gamma(i)$ is the full time window, no optimality or cost assumption is needed; the paper's proof uses optimality only to place $t_q$ in the narrower set of §6.1.3.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), pp. 1659–1660, Lemma 6

import Mathlib
import Definitions.Def_RunwayCPS_DiscreteTime_ModifiedNetwork

namespace RunwayCPS.DiscreteTime

/-- Lemma 6 (p. 1659), in the stronger form for every feasible schedule: when `k ≥ 1`, every
feasible schedule `(σ, t)` (separations need not satisfy the triangle inequality) is
represented by a source-sink path of the modified network, i.e. there is a path whose
sequence is `σ` and whose landing times are `t`. In particular every optimal schedule is. -/
theorem lemma_6 {n : ℕ} [NeZero n] (I : Instance n) (hk : 1 ≤ I.k)
    (σ : Fin n → Fin n) (t : Fin n → ℕ) (h : IsFeasible I σ t) :
    ∃ P : ℕ → MNode n, IsMPath I P ∧ mSeq P = σ ∧ mTimes P = t := by sorry

end RunwayCPS.DiscreteTime
