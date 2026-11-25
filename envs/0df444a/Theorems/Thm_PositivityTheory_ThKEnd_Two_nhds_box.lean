-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_nhds_box
-- name    : PositivityTheory.ThKEnd.Two.nhds_box
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:48.405114+00:00
-- url     : https://prove2.me/theorems/e56e03e4-2175-463f-818e-3cd13c1b46c7
-- title:
--   Two: nhds box
-- statement:
--   The Two construction uses the nhds box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L54-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L54-L66

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

theorem PositivityTheory.ThKEnd.Two.nhds_box {W : Set SL(2, R)} (hW : W ∈ 𝓝 1) : ∃ O ∈ 𝓝 (0 : R), ∀ y : SL(2, R), (∀ i j, (y.1 - 1) i j ∈ O) → y ∈ W := by sorry
