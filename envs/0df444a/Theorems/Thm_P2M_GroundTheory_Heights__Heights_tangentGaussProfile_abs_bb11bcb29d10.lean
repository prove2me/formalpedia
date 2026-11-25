-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_tangentGaussProfile_abs_bb11bcb29d10
-- name    : P2M_GroundTheory_Heights__Heights_tangentGaussProfile_abs_bb11bcb29d10
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:50:58.274396+00:00
-- url     : https://prove2.me/theorems/9bb92695-6b1c-45e4-968a-800ad58d6eff
-- title:
--   P2 M Ground Theory Heights  Heights tangent Gauss Profile abs bb11bcb29d10: P2 M Ground Theory Heights  Heights tangent Gauss Profile abs bb11bcb29d10
-- statement:
--   The P2 M Ground Theory Heights  Heights tangent Gauss Profile abs bb11bcb29d10 construction uses the P2 M Ground Theory Heights  Heights tangent Gauss Profile abs bb11bcb29d10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussMoment.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussMoment.lean#L24-L27

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

theorem P2M_GroundTheory_Heights__Heights_tangentGaussProfile_abs_bb11bcb29d10 (n m : ℕ) (r : ℝ) :
    tangentGaussProfile n m |r| = tangentGaussProfile n m r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«tangentGaussProfile_abs» := P2M_GroundTheory_Heights__Heights_tangentGaussProfile_abs_bb11bcb29d10
