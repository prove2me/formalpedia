-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_amgm_sum_ge
-- name    : ReciprocityTheory.ChartRestriction.G.I2.amgm_sum_ge
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:27:14.954364+00:00
-- url     : https://prove2.me/theorems/bc2e0f62-6b0c-5b53-bfb1-dae51f3ae5d1
-- title:
--   I2: amgm sum ge
-- statement:
--   The I2 construction uses the amgm sum ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVC.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVC.lean#L5-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitVC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2

theorem ReciprocityTheory.ChartRestriction.G.I2.amgm_sum_ge {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (P : ℝ) (hP : 0 ≤ P) (hprod : P ≤ ∏ i, a i) (hn : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) * P ^ ((Fintype.card ι : ℝ)⁻¹) ≤ ∑ i, a i := by sorry
