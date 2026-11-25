-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_linProj_smul_left_0afd722762be
-- name    : P2M_GroundTheory_Heights__Heights_linProj_smul_left_0afd722762be
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:42.369214+00:00
-- url     : https://prove2.me/theorems/b57b8ffe-8ce6-4803-bc16-fe80668923a1
-- title:
--   P2 M Ground Theory Heights  Heights lin Proj smul left 0afd722762be: P2 M Ground Theory Heights  Heights lin Proj smul left 0afd722762be
-- statement:
--   The P2 M Ground Theory Heights  Heights lin Proj smul left 0afd722762be construction uses the P2 M Ground Theory Heights  Heights lin Proj smul left 0afd722762be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussMoment.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentGaussMoment.lean#L14-L16

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

theorem P2M_GroundTheory_Heights__Heights_linProj_smul_left_0afd722762be {m n : ℕ} (π : Fin m → Fin n → ℂ) (c : ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    linProj π (c • y) = c • linProj π y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«linProj_smul_left» := P2M_GroundTheory_Heights__Heights_linProj_smul_left_0afd722762be
