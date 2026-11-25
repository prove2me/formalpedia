-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_dia_val
-- name    : PositivityTheory.ThKEnd.Two.dia_val
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:32.807849+00:00
-- url     : https://prove2.me/theorems/d6e8032a-31f0-4b4e-8298-0101a161b42f
-- title:
--   Two: dia val
-- statement:
--   The Two construction uses the dia val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L32-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L32-L32

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

theorem PositivityTheory.ThKEnd.Two.dia_val (u : Rˣ) : (dia u).1 = !![u.1, 0; 0, (u⁻¹).1] := by sorry
