-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SquareNormBall_box_subset_sqBall
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.box_subset_sqBall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:54.18503+00:00
-- url     : https://prove2.me/theorems/a1d57ca0-7402-45d7-ada8-715aa91591d7
-- title:
--   Square Norm Ball: box subset sq Ball
-- statement:
--   The Square Norm Ball construction uses the box subset sq Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidStA.lean#L59-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidStA.lean#L59-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_EllipsoidStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.box_subset_sqBall (r : ℕ) {R : ℝ} :
    Set.pi Set.univ (fun _ : Fin r => Metric.closedBall (0 : E) (R / Real.sqrt r)) ⊆
      sqBall r E R := by sorry
