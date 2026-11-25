-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paNum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.paNum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:10.061197+00:00
-- url     : https://prove2.me/theorems/059e8699-6fdf-4c73-aa31-01a783645556
-- title:
--   I2: pa Num
-- statement:
--   The I2 construction uses the pa Num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L277-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAB.lean#L277-L310

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropABSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaThContinuous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.paNum (g : ℕ) (c R0 : ℝ) (hc : 0 ≤ c) (h270 : 270 ≤ R0 ^ 2)
    (h90 : 90 * ((g : ℝ) + c) ≤ R0 ^ 2) :
    2 ^ (1 + 3 * ((g : ℝ) + c) / 2) * (2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16)) ≤ 1 / 2 := by sorry
