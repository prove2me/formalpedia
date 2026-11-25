-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_exp_quarter
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cab_exp_quarter
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:28:28.78822+00:00
-- url     : https://prove2.me/theorems/8cc75c27-f1d0-4f3a-85db-30611a83ed80
-- title:
--   I2: cab exp quarter
-- statement:
--   The I2 construction uses the cab exp quarter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L171-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelB.lean#L171-L173

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.I2.cab_exp_quarter : (1.28 : ℝ) ≤ Real.exp (1 / 4) := by sorry
