-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paPoly_growth
-- name    : ReciprocityTheory.ChartRestriction.G.I2.paPoly_growth
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:16.27225+00:00
-- url     : https://prove2.me/theorems/208bc9a0-dd39-43ad-ab9d-8fb0ac4ba4e8
-- title:
--   I2: pa Poly growth
-- statement:
--   The I2 construction uses the pa Poly growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L125-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean#L125-L145

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

theorem ReciprocityTheory.ChartRestriction.G.I2.paPoly_growth {c : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v, ‖F v‖ ≤ C * (1 + ‖v‖) ^ c := by sorry
