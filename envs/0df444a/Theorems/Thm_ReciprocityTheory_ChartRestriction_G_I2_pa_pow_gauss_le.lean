-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pa_pow_gauss_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.pa_pow_gauss_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:58.180941+00:00
-- url     : https://prove2.me/theorems/335b3219-ec2e-4c66-8d25-6ea9a2c41ef2
-- title:
--   I2: pa pow gauss le
-- statement:
--   The I2 construction uses the pa pow gauss le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L171-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L171-L184

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
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

theorem ReciprocityTheory.ChartRestriction.G.I2.pa_pow_gauss_le (n : ℕ) {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    (1 + t) ^ n * Real.exp (-b * t ^ 2) ≤
      2 ^ n * (2 + n.factorial * (2 / b) ^ n) * Real.exp (-(b / 2) * t ^ 2) := by sorry
