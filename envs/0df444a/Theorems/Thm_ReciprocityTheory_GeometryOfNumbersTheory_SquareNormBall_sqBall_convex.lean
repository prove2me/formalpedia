-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SquareNormBall_sqBall_convex
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.sqBall_convex
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:58.011515+00:00
-- url     : https://prove2.me/theorems/57ab414e-677f-4ab3-bf5a-b3c6848fa6fa
-- title:
--   Square Norm Ball: sq Ball convex
-- statement:
--   The Square Norm Ball construction uses the sq Ball convex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidStA.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidStA.lean#L26-L35

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.sqBall_convex (r : ℕ) (R : ℝ) : Convex ℝ (sqBall r E R) := by sorry
