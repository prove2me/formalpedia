-- Prove2me | Theorems.Thm_SingleMachineSched_LPRelax_corollary_2_6
-- name    : SingleMachineSched.LPRelax.corollary_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T04:29:09.499414+00:00
-- url     : https://prove2.me/theorems/05f297b3-ee62-48de-bea7-b5bb854544fc
-- title:
--   Corollary 2.6 — $Z_D = Z_R$ for all weights $w \ge 0$
-- statement:
--   Let $n$ jobs have integral processing times $p_j > 0$, integral release dates $r_j \ge 0$ and weights $w_j \ge 0$, and let the horizon $T \in \mathbb N$ bound the makespan of some feasible nonpreemptive schedule. Then the preemptive time-indexed relaxation (D) with horizon $T$ and the mean busy time relaxation (R) have the same optimal value:
--
--   $$Z_D = Z_R .$$
--
--   Both are lower bounds on the optimum of $1\,|\,r_j\,|\,\sum w_j C_j$. The equality means that the pseudopolynomial LP (D) and the exponentially constrained LP (R) give the same bound, and that both are attained by the LP schedule; the approximation results of the paper are measured against this common value.
--
--   **Formalization Note** No ordering of the jobs is assumed: the statement holds for every nonnegative weight vector, and the LP schedule does not appear in it. The paper takes $T$ to be an upper bound on the makespan of an optimal schedule; here $T$ is only required to bound the makespan of *some* feasible nonpreemptive schedule (with real start times), which every such $T$ does, so the statement covers the paper's. The paper's second sentence, that the common value can be computed in $O(n \log n)$ time, is a running-time claim and is not formalized.
-- source:
--   Goemans, Queyranne, Schulz, Skutella & Wang, Single Machine Scheduling with Release Dates, SIAM J. Discrete Math. 15(2) (2002), p. 173, Corollary 2.6

import Mathlib
import Definitions.Def_SingleMachineSched_Shared_RelaxationR
import Definitions.Def_SingleMachineSched_LPRelax_RelaxationD

namespace SingleMachineSched.LPRelax

/-- Corollary 2.6: for any nonnegative weights, the preemptive time-indexed relaxation (D) and
the mean busy time relaxation (R) have the same optimal value, `Z_D = Z_R`. -/
theorem corollary_2_6 {n : ℕ} (p r : Fin n → ℕ) (w : Fin n → ℝ) (T : ℕ)
    (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j) (hT : IsMakespanBound p r T) :
    zD p r w T = Shared.zR p r w := by sorry

end SingleMachineSched.LPRelax
