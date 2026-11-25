-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_sum_ge_of_prod_ge
-- name    : ReciprocityTheory.ChartRestriction.G.I2.sum_ge_of_prod_ge
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:30:34.763309+00:00
-- url     : https://prove2.me/theorems/d43321bb-298c-49aa-a6ac-6b03fc724880
-- title:
--   I2: sum ge of prod ge
-- statement:
--   The I2 construction uses the sum ge of prod ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVC.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/SplitVC.lean#L28-L32

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

theorem ReciprocityTheory.ChartRestriction.G.I2.sum_ge_of_prod_ge {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (D : ℝ) (hD : 0 < D) (hprod : (D ^ 2)⁻¹ ≤ ∏ i, a i) (hn : 0 < Fintype.card ι) :
    (Fintype.card ι : ℝ) / (D ^ ((Fintype.card ι : ℝ)⁻¹)) ^ 2 ≤ ∑ i, a i := by sorry
