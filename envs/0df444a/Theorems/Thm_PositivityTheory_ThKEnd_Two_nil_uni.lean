-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_nil_uni
-- name    : PositivityTheory.ThKEnd.Two.nil_uni
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:38.646817+00:00
-- url     : https://prove2.me/theorems/d2f17947-67e6-470b-9905-3f0188c29067
-- title:
--   Two: nil uni
-- statement:
--   The Two construction uses the nil uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L106-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L106-L110

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

theorem PositivityTheory.ThKEnd.Two.nil_uni (y : SL(2, R)) (w : R) : !![0, 1; 0, 0] * ((uni (.ofAdd w))⁻¹ * y).1 = !![0, 1; 0, 0] * y.1 := by sorry
