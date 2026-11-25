-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_diff_uni
-- name    : PositivityTheory.ThKEnd.Two.diff_uni
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:24.205452+00:00
-- url     : https://prove2.me/theorems/7f616216-ef3f-585b-aa06-7c82aa649491
-- title:
--   Two: diff uni
-- statement:
--   The Two construction uses the diff uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L95-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L95-L104

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

theorem PositivityTheory.ThKEnd.Two.diff_uni (κ y : SL(2, R)) (w : R) :
    (κ⁻¹ * y).1 - (κ⁻¹ * ((uni (.ofAdd w))⁻¹ * y)).1 = w • ((κ⁻¹).1 * !![0, 1; 0, 0] * y.1) := by sorry
