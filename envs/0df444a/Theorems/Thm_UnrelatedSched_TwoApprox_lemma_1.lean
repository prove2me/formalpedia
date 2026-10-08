-- Prove2me | Theorems.Thm_UnrelatedSched_TwoApprox_lemma_1
-- name    : UnrelatedSched.TwoApprox.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:45:19.324832+00:00
-- url     : https://prove2.me/theorems/0f8d81cf-f5d2-478a-9c51-ab0138804629
-- title:
--   Lemma 1 — binary search with a ρ-relaxed decision procedure is a ρ-approximation algorithm
-- statement:
--   Let $m\ge 1$ machines and $n$ jobs have processing times $p_{ij}$ that are positive integers, and let $\mathrm{OPT}$ be the minimum makespan. Let $\rho\in\mathbb R$ and let $D$ be a $\rho$-relaxed decision procedure for this instance. Then the schedule $\sigma_D$ output by the binary search of Lemma 1 driven by $D$ satisfies
--   $$\operatorname{makespan}(\sigma_D)\le\rho\cdot\mathrm{OPT}.$$
--
--   The lemma reduces the design of a $\rho$-approximation algorithm to the design of a $\rho$-relaxed decision procedure, which only has to answer the decision question approximately for one deadline at a time.
--
--   **Formalization Note** The paper states: "If there is a polynomial $\rho$-relaxed decision procedure ..., then there is a polynomial $\rho$-approximation algorithm". Its proof establishes that the binary search outputs a schedule within $\rho\cdot\mathrm{OPT}$, which is what is formalized; the polynomial running time is not. The procedure is evaluated at natural-number deadlines, which suffices because $\mathrm{OPT}$ is an integer. No hypothesis $\rho\ge 1$ is needed: when $n\ge 1$ no $\rho$-relaxed procedure with $\rho<1$ exists (it would have to beat the optimum at $d=\mathrm{OPT}$), and when $n=0$ every makespan is $0$. $\mathrm{OPT}$ is the makespan of an optimal schedule `σopt`.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 5, Lemma 1 and its proof

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP
import Definitions.Def_UnrelatedSched_TwoApprox_Algorithm

namespace UnrelatedSched.TwoApprox

open MatousekLP.Scheduling

/-- Lemma 1, p. 5: the binary search driven by a `ρ`-relaxed decision procedure outputs a schedule
of makespan at most `ρ` times the optimum. -/
theorem lemma_1 {m n : ℕ} (hm : 0 < m) (P : Matrix (Fin m) (Fin n) ℕ) (hP : ∀ i j, 0 < P i j)
    (ρ : ℝ) (D : DecisionProcedure m n) (hD : IsRelaxedDecisionProcedure P ρ D)
    (σopt : Fin n → Fin m) (hopt : IsOptimalSchedule (realTimes P) σopt) :
    makespan (realTimes P) (binarySearch P hm D) ≤ ρ * makespan (realTimes P) σopt := by sorry

end UnrelatedSched.TwoApprox
