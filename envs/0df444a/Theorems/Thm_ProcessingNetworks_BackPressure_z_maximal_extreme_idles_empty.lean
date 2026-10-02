-- Prove2me | Theorems.Thm_ProcessingNetworks_BackPressure_z_maximal_extreme_idles_empty
-- name    : ProcessingNetworks.BackPressure.z_maximal_extreme_idles_empty
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T18:44:25.04586+00:00
-- url     : https://prove2.me/theorems/6321262d-d960-485e-aa41-c79473a18a16
-- title:
--   Lemma 9.10 — a z-maximal extreme allocation idling empty buffers (milestone)
-- statement:
--   **Lemma 9.10.** For any $z \in \mathbb{R}^I_+$, there is a $z$-maximal extreme allocation
--   $\beta(z) \in E$ with $\beta_j(z) = 0$ whenever activity $j$'s buffer is empty.
--
--   Even at the fluid level, where an activity serving an empty buffer *could* still run at a
--   positive rate (Section 9.5's tandem-model illustration), one can always choose an optimal
--   allocation that declines to do so — this is Lemma 9.11's key ingredient for showing dominated
--   allocations are genuinely infeasible, not merely suboptimal.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 174, Lemma 9.10

import Mathlib
import Definitions.Def_ProcessingNetworks_BackPressure_SPNPlanningData
import Definitions.Def_ProcessingNetworks_BackPressure_LeontiefNetwork
import Definitions.Def_ProcessingNetworks_BackPressure_AllocationPolytope

namespace ProcessingNetworks.BackPressure

/-- Lemma 9.10, Dai & Harrison p. 174 (PDF p. 190): consider an SPN whose data satisfy
Assumption 9.1. For any `z ∈ ℝ^I_+` there is a `z`-maximal extreme allocation `β(z) ∈ E` with
`β_j(z) = 0` for every activity `j` whose served buffer is empty (`z_{i(j)} = 0`). -/
theorem z_maximal_extreme_idles_empty
    {I J K : ℕ} (dat : SPNPlanningData I J K) (h91 : SatisfiesAssumption91 dat)
    (z : Fin I → ℝ) (hz : ∀ i, 0 ≤ z i) :
    ∃ β ∈ ExtremeAllocations dat, IsZMaximal dat β z ∧
      ∀ j : Fin J, z (servesBuffer h91 j) = 0 → β j = 0 := by sorry

end ProcessingNetworks.BackPressure
