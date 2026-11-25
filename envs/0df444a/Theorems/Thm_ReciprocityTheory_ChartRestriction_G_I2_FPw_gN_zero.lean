-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_gN_zero
-- name    : ReciprocityTheory.ChartRestriction.G.I2.FPw.gN_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:55.362599+00:00
-- url     : https://prove2.me/theorems/ce820fa3-e16f-48c6-a5e7-7fddbc0b19df
-- title:
--   FPw: g N zero
-- statement:
--   The FPw construction uses the g N zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/IteratedFDerivTailZero.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/IteratedFDerivTailZero.lean#L58-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_IteratedFDerivTailZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.FPw.gN_zero (N : ℕ) : gN N 0 = 0 := by sorry
