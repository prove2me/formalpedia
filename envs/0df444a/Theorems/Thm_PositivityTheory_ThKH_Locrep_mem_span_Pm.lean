-- Prove2me | Theorems.Thm_PositivityTheory_ThKH_Locrep_mem_span_Pm
-- name    : PositivityTheory.ThKH.Locrep.mem_span_Pm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:01:16.945111+00:00
-- url     : https://prove2.me/theorems/d089402c-9c9f-48cb-a322-9b1d220d726e
-- title:
--   Locrep: mem span Pm
-- statement:
--   The Locrep construction uses the mem span Pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LocrepSB.lean#L72-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/LocalThetaKernels/LocrepSB.lean#L72-L176

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

theorem PositivityTheory.ThKH.Locrep.mem_span_Pm (h : ∀ y, ev (ι y) = y) (hev : Continuous ev) (hι : Continuous ι) {g : A → ℂ} (hg : g ∈ SB A) :
    g ∈ Submodule.span ℂ {f | ∃ φ ∈ SB K, ∃ y, f = Pm ev ι φ y g} := by sorry
