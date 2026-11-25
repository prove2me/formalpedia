-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pa_one_add_pow_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.pa_one_add_pow_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:33.398237+00:00
-- url     : https://prove2.me/theorems/89095bab-794e-5182-8059-40d75033e1e3
-- title:
--   I2: pa one add pow le
-- statement:
--   The I2 construction uses the pa one add pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L161-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L161-L169

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

theorem ReciprocityTheory.ChartRestriction.G.I2.pa_one_add_pow_le (n : ℕ) {t : ℝ} (ht : 0 ≤ t) : (1 + t) ^ n ≤ 2 ^ n * (1 + t ^ n) := by sorry
