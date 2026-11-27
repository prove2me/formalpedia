-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Locrep_Pm_mem_SB
-- name    : PositivityTheory.ThKH.Locrep.Pm_mem_SB
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:12.992791+00:00
-- url     : https://prove2.me/theorems/b52becf5-6e87-4eb2-9ecf-37afff8eb41b
-- title:
--   Locrep: Pm mem SB
-- statement:
--   The Locrep construction uses the Pm mem SB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LocrepSB.lean#L46-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LocrepSB.lean#L46-L70

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

theorem PositivityTheory.ThKH.Locrep.Pm_mem_SB (h : ∀ y, ev (ι y) = y) (hev : Continuous ev) (hι : Continuous ι) {φ : K → ℂ} (hφ : φ ∈ SB K) (y : K)
    {g : A → ℂ} (hg : g ∈ SB A) : Pm ev ι φ y g ∈ SB A := by sorry
