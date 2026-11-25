-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SquareNormBall_norm_sq_convex_comb
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.norm_sq_convex_comb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:52:41.075811+00:00
-- url     : https://prove2.me/theorems/530ac725-a96b-5a46-a035-e74087ba6e6b
-- title:
--   Square Norm Ball: norm sq convex comb
-- statement:
--   The Square Norm Ball construction uses the norm sq convex comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidStA.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/LatticeCovolumes/EllipsoidStA.lean#L14-L24

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.SquareNormBall.norm_sq_convex_comb {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (z w : E) :
    ‖a • z + b • w‖ ^ 2 ≤ a * ‖z‖ ^ 2 + b * ‖w‖ ^ 2 := by sorry
