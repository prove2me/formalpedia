-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_gaussianInner_integrable
-- name    : ReciprocityTheory.ChartRestriction.G.I2.gaussianInner_integrable
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:14.010749+00:00
-- url     : https://prove2.me/theorems/6adc2bbd-6414-4491-bfb0-d30ebe2094c9
-- title:
--   I2: gaussian Inner integrable
-- statement:
--   The I2 construction uses the gaussian Inner integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L209-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L209-L220

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

theorem ReciprocityTheory.ChartRestriction.G.I2.gaussianInner_integrable {q c : ℕ} (hq : 1 ≤ q) {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) :
    Integrable (fun v => F v * (starRingEnd ℂ) (G v) * (paW q v : ℂ)) := by sorry
