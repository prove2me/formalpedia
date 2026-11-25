-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Two_uni_dia
-- name    : PositivityTheory.ThKEnd.Two.uni_dia
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:50:41.277709+00:00
-- url     : https://prove2.me/theorems/b4f16749-1db8-48cc-8543-97b7c69873f8
-- title:
--   Two: uni dia
-- statement:
--   The Two construction uses the uni dia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ClosedEmb.lean#L34-L39

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

theorem PositivityTheory.ThKEnd.Two.uni_dia (x : R) (u : Rˣ) : uni (.ofAdd x) * dia u = dia u * uni (.ofAdd ((u⁻¹).1 * (u⁻¹).1 * x)) := by sorry
