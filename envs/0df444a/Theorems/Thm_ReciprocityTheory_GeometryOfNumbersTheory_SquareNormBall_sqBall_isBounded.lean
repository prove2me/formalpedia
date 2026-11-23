-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SquareNormBall_sqBall_isBounded
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.sqBall_isBounded
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:52:14.568438+00:00
-- url     : https://prove2.me/theorems/c4a12859-f42c-4de4-b301-bf9e46c80a16
-- title:
--   Square Norm Ball: sq Ball is Bounded
-- statement:
--   The Square Norm Ball construction uses the sq Ball is Bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidStA.lean#L52-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidStA.lean#L52-L52

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.sqBall_isBounded (r : ℕ) (R : ℝ) : Bornology.IsBounded (sqBall r E R) := by sorry
