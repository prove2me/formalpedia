-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_box
-- name    : PositivityTheory.ThKEnd.Two.box
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:14.170914+00:00
-- url     : https://prove2.me/theorems/4ad7f5a1-287f-51b6-840e-1a54e95e8eaf
-- title:
--   Two: box
-- statement:
--   The Two construction uses the box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L50-L52

import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ClosedEmb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter Matrix NumberField IsDedekindDomain
open scoped Pointwise MatrixGroups
variable {R : Type} [CommRing R]
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem PositivityTheory.ThKEnd.Two.box [T2Space R] {C : Fin 2 → Fin 2 → Set R} (h : ∀ i j, IsCompact (C i j)) :
    IsCompact {g : SL(2, R) | ∀ i j, g.1 i j ∈ C i j} := by sorry
