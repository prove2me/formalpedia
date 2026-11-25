-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_volume_null_of_hausdorff_null_a26ea8030678
-- name    : P2M_GroundTheory_Heights__Heights_volume_null_of_hausdorff_null_a26ea8030678
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:52:22.4768+00:00
-- url     : https://prove2.me/theorems/0d779c36-090b-44bc-9629-a30ffbf3380e
-- title:
--   P2 M Ground Theory Heights  Heights volume null of hausdorff null a26ea8030678: P2 M Ground Theory Heights  Heights volume null of hausdorff null a26ea8030678
-- statement:
--   The P2 M Ground Theory Heights  Heights volume null of hausdorff null a26ea8030678 construction uses the P2 M Ground Theory Heights  Heights volume null of hausdorff null a26ea8030678 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeAreaFormula.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PConeAreaFormula.lean#L13-L22

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

theorem P2M_GroundTheory_Heights__Heights_volume_null_of_hausdorff_null_a26ea8030678 {m : ℕ} {s : Set (EuclideanSpace ℂ (Fin m))}
    (hs : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) s = 0) : volume s = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«volume_null_of_hausdorff_null» := P2M_GroundTheory_Heights__Heights_volume_null_of_hausdorff_null_a26ea8030678
