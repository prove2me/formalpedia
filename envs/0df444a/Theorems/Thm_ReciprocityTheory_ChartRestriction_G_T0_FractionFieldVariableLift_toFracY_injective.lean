-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FractionFieldVariableLift_toFracY_injective
-- name    : ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.toFracY_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:36:31.970525+00:00
-- url     : https://prove2.me/theorems/e2c87776-cee3-4a4a-a489-61360226b86d
-- title:
--   Fraction Field Variable Lift: to Frac Y injective
-- statement:
--   The Fraction Field Variable Lift construction uses the to Frac Y injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteDimensionalOfLiftY.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteDimensionalOfLiftY.lean#L34-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisExtend
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteDimensionalOfLiftY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift
open MvPolynomial
variable {A : Type} [CommRing A] [IsDomain A] {σ : Type}

theorem ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.toFracY_injective : Function.Injective (toFracY A σ) := by sorry
