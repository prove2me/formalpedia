-- Prove2me | Theorems.Thm_PrimalDualLDR_Multistage_theorem_3_primal
-- name    : PrimalDualLDR.Multistage.theorem_3_primal
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-05T17:11:26.765695+00:00
-- url     : https://prove2.me/theorems/b0f20fd4-36bd-422f-ac5b-10296ebebf32
-- title:
--   Theorem 3, primal part — $\mathcal{MSP}^u$ is equivalent to the linear program (4.2)
-- statement:
--   Consider the linear multistage stochastic program $\mathcal{MSP}$ of §4 with deterministic constraint matrices $A_{ts}$, right-hand sides $b_t(\xi^t) = B_tP_t\xi$ and costs $c_t(\xi^t) = C_tP_t\xi$, and assume that $\mathbb P$ has a polyhedral support $\Xi = \{\xi : W\xi \ge h\}$ of the type (2.1) (nonempty, bounded, spanning $\mathbb R^k$, with $W,h$ of the form (2.1b) and $k_1 = 1$). Fix matrices $M_t \in \mathbb R^{k\times k^t}$.
--
--   The primal linear-decision-rule problem
--   $$\mathcal{MSP}^u:\quad \min \sum_t \operatorname{Tr}(P_tMP_t^\top C_t^\top X_t)\ \text{ s.t. }\ \sum_s A_{ts}X_sP_sM_tP_t\xi + S_tP_t\xi = B_tP_t\xi,\ \ S_tP_t\xi \ge 0\ \ \mathbb P\text{-a.s.}\ \forall t$$
--   has the same optimal value as the linear program
--   $$(4.2):\quad \min \sum_t \operatorname{Tr}(P_tMP_t^\top C_t^\top X_t)\ \text{ s.t. }\ \sum_s A_{ts}X_sP_sM_tP_t + \Lambda_tW = B_tP_t,\ \ \Lambda_th \ge 0,\ \ \Lambda_t \ge 0\ \ \forall t.$$
--
--   Optimal values are infima in the extended reals ($+\infty$ if infeasible, $-\infty$ if unbounded). This is the first assertion of Theorem 3; it needs only the support assumptions (the conditional-mean and strict-feasibility hypotheses of Theorem 3 are not used, so they are omitted, which makes the statement slightly stronger). The proof is the robust-counterpart argument of §2: an almost surely nonnegative linear function is nonnegative on the support $\Xi$, and by the affine Farkas lemma this is equivalent to the existence of the multipliers $\Lambda_t$.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 22, Theorem 3 (first assertion: MSP^u is equivalent to (4.2)); the argument parallels Theorem 1 / (2.3), pp. 5-6

import Mathlib
import Definitions.Def_PrimalDualLDR_Multistage_Basic
import Definitions.Def_PrimalDualLDR_Multistage_Setting
import Definitions.Def_PrimalDualLDR_Multistage_Problems

open MeasureTheory Matrix

namespace PrimalDualLDR.Multistage

/-- Theorem 3 (p. 22), first assertion: if `P` has a polyhedral support of the type (2.1) (the
standing assumptions of §4), then the primal linear-decision-rule problem `𝓜𝒮𝒫^u` and the linear
program (4.2) have the same optimal value. Only the standing assumptions are needed for this half;
the linear-conditional-mean and strict-feasibility hypotheses of Theorem 3 are not used. -/
theorem theorem_3_primal (σ : Setting) (hσ : σ.Standing) :
    σ.valMSPu = σ.valLP42 := by sorry

end PrimalDualLDR.Multistage
