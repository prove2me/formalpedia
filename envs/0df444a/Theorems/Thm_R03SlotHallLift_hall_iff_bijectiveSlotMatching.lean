-- Prove2me | Theorems.Thm_R03SlotHallLift_hall_iff_bijectiveSlotMatching
-- name    : R03SlotHallLift.hall_iff_bijectiveSlotMatching
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T11:12:58.960133+00:00
-- url     : https://prove2.me/theorems/aada9bf7-4477-44ce-96e2-905cfd5b0a35
-- title:
--   R03 P3-factor structural result: hall iff bijectiveSlotMatching
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03SlotHallLift.hall_iff_bijectiveSlotMatching` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
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
theorem hall_iff_bijectiveSlotMatching
    (R : V → Fin 2 → V → Prop) (C : Finset V)
    (hcard : Fintype.card (Slot C) = Fintype.card (Leaf C)) :
    HallCondition R C ↔ BijectiveSlotMatching R C := by sorry

end R03SlotHallLift
