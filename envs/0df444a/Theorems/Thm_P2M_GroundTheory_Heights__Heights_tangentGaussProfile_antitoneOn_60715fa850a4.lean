-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_tangentGaussProfile_antitoneOn_60715fa850a4
-- name    : P2M_GroundTheory_Heights__Heights_tangentGaussProfile_antitoneOn_60715fa850a4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:40.880501+00:00
-- url     : https://prove2.me/theorems/c01ba744-74ca-4e3f-ac36-5fb49f2fd4f0
-- title:
--   P2 M Ground Theory Heights  Heights tangent Gauss Profile antitone On 60715fa850a4: P2 M Ground Theory Heights  Heights tangent Gauss Profile antitone On 60715fa850a4
-- statement:
--   The P2 M Ground Theory Heights  Heights tangent Gauss Profile antitone On 60715fa850a4 construction uses the P2 M Ground Theory Heights  Heights tangent Gauss Profile antitone On 60715fa850a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussMoment.lean#L29-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussMoment.lean#L29-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadPlaneJac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentGaussMoment
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_tangentGaussProfile_antitoneOn_60715fa850a4 (n m : ℕ) :
    AntitoneOn (tangentGaussProfile n m) (Set.Ici 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«tangentGaussProfile_antitoneOn» := P2M_GroundTheory_Heights__Heights_tangentGaussProfile_antitoneOn_60715fa850a4
