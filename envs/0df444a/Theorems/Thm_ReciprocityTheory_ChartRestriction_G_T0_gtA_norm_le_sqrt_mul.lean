-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_gtA_norm_le_sqrt_mul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.gtA_norm_le_sqrt_mul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:38:05.350306+00:00
-- url     : https://prove2.me/theorems/f72f464e-c64a-43f1-96ca-1a128cfe478b
-- title:
--   T0: gt A norm le sqrt mul
-- statement:
--   The T0 construction uses the gt A norm le sqrt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L56-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TransferenceA.lean#L56-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TransferenceA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory Module Submodule

theorem ReciprocityTheory.ChartRestriction.G.T0.gtA_norm_le_sqrt_mul (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ≤ Real.sqrt n * ‖EuclideanSpace.equiv (Fin n) ℝ x‖ := by sorry
