-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pa_integrable_of_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.pa_integrable_of_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:27.507912+00:00
-- url     : https://prove2.me/theorems/7868e8af-3960-4075-8c08-48a0682af997
-- title:
--   I2: pa integrable of le
-- statement:
--   The I2 construction uses the pa integrable of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L186-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L186-L194

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

theorem ReciprocityTheory.ChartRestriction.G.I2.pa_integrable_of_le {E' : Type*} [NormedAddCommGroup E'] {f : EuclideanSpace ℂ ι → E'}
    (hf : Continuous f) (n : ℕ) {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (h : ∀ v, ‖f v‖ ≤ C * ((1 + ‖v‖) ^ n * Real.exp (-b * ‖v‖ ^ 2))) : Integrable f := by sorry
