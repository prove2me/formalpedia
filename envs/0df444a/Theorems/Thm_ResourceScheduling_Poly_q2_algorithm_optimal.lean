-- Prove2me | Theorems.Thm_ResourceScheduling_Poly_q2_algorithm_optimal
-- name    : ResourceScheduling.Poly.q2_algorithm_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:34:23.830502+00:00
-- url     : https://prove2.me/theorems/2e2fda2b-052e-4504-8df2-e642a3deffec
-- title:
--   Theorem 5 (correctness of the algorithm) — the two-machine algorithm is optimal for Q2 | res1··, p_j = 1 | C_max
-- statement:
--   Consider $Q2\mid res1{\cdot}{\cdot},\,p_j=1\mid C_{\max}$: two uniform machines $M_1,M_2$ with speeds $q_1\ge q_2>0$, one resource $R_1$ of positive integer size $s_1$, $n$ unit-time jobs $J_j$ with nonnegative integer requirements $r_{1j}\le s_1$, and no precedence constraints. Let $\pi$ be any order of the jobs with nonincreasing requirements, and let $A$ be the schedule produced from $\pi$ by the algorithm of Theorem 5: schedule all jobs on $M_1$ in the order $\pi$, then successively remove the last job from $M_1$ and schedule it as early as possible on $M_2$, as long as this reduces $C_{\max}$.
--
--   Then $A$ is feasible and optimal:
--   $$C_{\max}(A)\le C_{\max}(\sigma)\qquad\text{for every feasible schedule } \sigma.$$
--
--   This is the mathematical content of Theorem 5 ("$Q2\mid res1{\cdot}{\cdot},\,p_j=1\mid C_{\max}$ is solvable in $O(n\log n)$ time"): together with Theorem 6, it settles every special case of $Q\mid res{\cdot}{\cdot}{\cdot},\,p_j=1\mid C_{\max}$ left open by the paper's hardness results.
--
--   **Formalization Note** The running time $O(n\log n)$ is not formalized; the statement is the correctness of the algorithm, for every nonincreasing order (ties broken arbitrarily). The hypothesis $r_{1j}\le s_1$ is implicit in the paper. Machines $M_1,M_2$ and resource $R_1$ are indices $0,1$ and $0$.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 16, Theorem 5 and its proof ("an optimal schedule can be obtained in the following way")

import Mathlib
import Definitions.Def_ResourceScheduling_Poly_Model
import Definitions.Def_ResourceScheduling_Poly_Q2Properties
import Definitions.Def_ResourceScheduling_Poly_Q2Algorithm

namespace ResourceScheduling.Poly

/-- Theorem 5 (p. 16), correctness of its algorithm: for `Q2 | res1··, p_j = 1 | C_max` with
`q_1 ≥ q_2`, every job fitting alone, and any job order of nonincreasing requirement, the
algorithm's schedule is feasible and has the minimum makespan among all feasible schedules. -/
theorem q2_algorithm_optimal (I : Instance) (hm : I.m = 2) (hl : I.l = 1)
    (hprec : I.NoPrecedence) (hq : I.q (I.M₂ hm) ≤ I.q (I.M₁ hm)) (hfit : I.EveryJobFits)
    (ord : Fin I.n ≃ Fin I.n) (hord : Antitone fun p => I.r (I.R₁ hl) (ord p)) :
    (q2Algorithm I hm hl ord).Feasible ∧
      ∀ σ : Schedule I, σ.Feasible → (q2Algorithm I hm hl ord).makespan ≤ σ.makespan := by sorry

end ResourceScheduling.Poly
