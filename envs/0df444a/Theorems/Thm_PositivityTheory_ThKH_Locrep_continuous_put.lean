-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Locrep_continuous_put
-- name    : PositivityTheory.ThKH.Locrep.continuous_put
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:00:52.097812+00:00
-- url     : https://prove2.me/theorems/7fce3109-916b-5242-81a4-f354608cf87f
-- title:
--   Locrep: continuous put
-- statement:
--   The Locrep construction uses the continuous put property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LocrepSB.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LocrepSB.lean#L41-L43

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_LocrepSB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Locrep
open Filter Topology GlobalTheory.WeilM
variable {A K : Type} [AddCommGroup A] [AddCommGroup K] (ev : A →+ K) (ι : K →+ A)
variable {ev ι}
variable [TopologicalSpace A] [IsTopologicalAddGroup A] [TopologicalSpace K] [IsTopologicalAddGroup K]
omit [IsTopologicalAddGroup K]

theorem PositivityTheory.ThKH.Locrep.continuous_put (hev : Continuous ev) (hι : Continuous ι) : Continuous fun p : A × K => put ev ι p.1 p.2 := by sorry
