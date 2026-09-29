-- Prove2me | Theorems.Thm_R03SlotHallLift_p3Factor_iff_exists_graph_center_hall
-- name    : R03SlotHallLift.p3Factor_iff_exists_graph_center_hall
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T11:13:36.162829+00:00
-- url     : https://prove2.me/theorems/bc8e3fed-7f29-4e5a-b358-e14e235a046b
-- title:
--   R03 P3-factor structural result: p3Factor iff exists graph center hall
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03SlotHallLift.p3Factor_iff_exists_graph_center_hall` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is e3441a213d0117aa98b20496f06271d32a980bee1873a72e371b345468f78fff.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp05/sp05_port_balanced_slot_factor_lift_formalization_v1.lean; source SHA-256 e3441a213d0117aa98b20496f06271d32a980bee1873a72e371b345468f78fff; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_809c83f713_sp05_port_balanced_slot_factor_lift_formalizatio

namespace R03SlotHallLift

open R03SlotHallLift
open CubicP3Partition
universe u
variable {V : Type u} [Fintype V]
open scoped Classical
theorem p3Factor_iff_exists_graph_center_hall
    (G : SimpleGraph V) :
    Nonempty (P3Factor G) ↔
      ∃ C : Finset V,
        Fintype.card V = 3 * C.card ∧ GraphCenterHallCondition G C := by sorry

end R03SlotHallLift
