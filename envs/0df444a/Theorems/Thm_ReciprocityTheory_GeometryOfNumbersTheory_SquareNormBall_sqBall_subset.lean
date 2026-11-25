-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SquareNormBall_sqBall_subset
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.sqBall_subset
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:51.509529+00:00
-- url     : https://prove2.me/theorems/7f5c2fa1-a5df-46c6-85ac-6298eb6a0a09
-- title:
--   Square Norm Ball: sq Ball subset
-- statement:
--   The Square Norm Ball construction uses the sq Ball subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidStA.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidStA.lean#L41-L50

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.sqBall_subset (r : ℕ) (R : ℝ) : sqBall r E R ⊆ Metric.closedBall 0 |R| := by sorry
