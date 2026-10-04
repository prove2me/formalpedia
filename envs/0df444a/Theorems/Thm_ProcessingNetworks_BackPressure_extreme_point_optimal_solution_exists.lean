-- Prove2me | Theorems.Thm_ProcessingNetworks_BackPressure_extreme_point_optimal_solution_exists
-- name    : ProcessingNetworks.BackPressure.extreme_point_optimal_solution_exists
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T18:30:54.154213+00:00
-- url     : https://prove2.me/theorems/3791473c-5d30-49c1-ad0b-111aec856161
-- title:
--   Proposition 9.6 — an extreme allocation is always optimal (milestone)
-- statement:
--   At each decision time, the system manager solves (9.15)-(9.17): maximize $p(\beta,\hat z)$
--   subject to $\beta \in \mathcal A$ and material availability $B(\hat n + u) \le \hat z$, where
--   $u$ (the service-initiation vector, Eq. 9.17) is determined from $\beta$ and $\hat n$.
--
--   **Proposition 9.6.** For each system state $(\hat n,\hat z) \in \mathbb{Z}^J_+\times
--   \mathbb{Z}^I_+$, an optimal solution of this problem can always be found among the extreme
--   allocations $E$.
--
--   This is what licenses restricting attention, at every decision time, to the finite set $E$
--   rather than the whole (continuum) polytope $\mathcal A$ — the basis for Remark 9.7's standing
--   convention.
--
--   **Formalization note.** `serviceInitiation` formalizes (9.17) directly; `BPFeasible` bundles
--   $\beta \in \mathcal A$ (Aβ≤b, β≥0) with the material-availability constraint (9.16)'s second
--   clause. The capacity consumption matrix is taken nonnegative with no zero column (Section 2.1's
--   binary $A$): this is what makes $\mathcal A$ bounded, so that the linear objective attains its
--   maximum at an extreme point — for an unbounded polytope the problem can have no optimal solution
--   at all, and the proposition would be false.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 170, Proposition 9.6

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope

namespace ProcessingNetworks.BackPressure

/-- Proposition 9.6, Dai & Harrison p. 170 (PDF p. 186): for each system state
`(n̂, ẑ) ∈ ℤ^J_+ × ℤ^I_+` there is an optimal solution of the back-pressure optimization problem
(9.15)-(9.17) that belongs to `E`, the set of extreme allocations. The capacity consumption
matrix is nonnegative with no zero column (Section 2.1's binary `A`), which is what makes the
allocation polytope bounded, so that the linear objective attains its maximum at an extreme
point. -/
theorem extreme_point_optimal_solution_exists
    {I J K : ℕ} (dat : SPNPlanningData I J K)
    (hA : ∀ k j, 0 ≤ dat.A k j) (hAcol : ∀ j, ∃ k, 0 < dat.A k j)
    (nhat : Fin J → ℕ) (zhat : Fin I → ℕ) :
    ∃ β ∈ ExtremeAllocations dat, BPFeasible dat nhat zhat β ∧
      ∀ β', BPFeasible dat nhat zhat β' →
        p dat β' (fun i => (zhat i : ℝ)) ≤ p dat β (fun i => (zhat i : ℝ)) := by sorry

end ProcessingNetworks.BackPressure
