-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_volume_linProj_image_null_7ac35fee0eee
-- name    : P2M_GroundTheory_Heights__Heights_volume_linProj_image_null_7ac35fee0eee
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:51:53.393469+00:00
-- url     : https://prove2.me/theorems/be0ff792-a9b5-4f46-af14-b55bf2c16e5b
-- title:
--   P2 M Ground Theory Heights  Heights volume lin Proj image null 7ac35fee0eee: P2 M Ground Theory Heights  Heights volume lin Proj image null 7ac35fee0eee
-- statement:
--   The P2 M Ground Theory Heights  Heights volume lin Proj image null 7ac35fee0eee construction uses the P2 M Ground Theory Heights  Heights volume lin Proj image null 7ac35fee0eee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeAreaFormula.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeAreaFormula.lean#L31-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeGraphCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeAreaFormula
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
open MeasureTheory Module
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_volume_linProj_image_null_7ac35fee0eee {m n : ℕ} (π : Fin m → Fin n → ℂ) {s : Set (EuclideanSpace ℂ (Fin n))}
    (hs : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) s = 0) : volume (linProj π '' s) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«volume_linProj_image_null» := P2M_GroundTheory_Heights__Heights_volume_linProj_image_null_7ac35fee0eee
