-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_gaussianInner_integrable_norm
-- name    : ReciprocityTheory.ChartRestriction.G.I2.gaussianInner_integrable_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:57:22.690902+00:00
-- url     : https://prove2.me/theorems/e3b85d1f-2b4e-4f43-8baf-1f15ad3565fe
-- title:
--   I2: gaussian Inner integrable norm
-- statement:
--   The I2 construction uses the gaussian Inner integrable norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L222-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L222-L226

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

theorem ReciprocityTheory.ChartRestriction.G.I2.gaussianInner_integrable_norm {q c : ℕ} (hq : 1 ≤ q) {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c)
    (hG : G ∈ paPoly c) : Integrable (fun v => ‖F v‖ * ‖G v‖ * paW q v) := by sorry
