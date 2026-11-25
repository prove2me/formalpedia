-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FractionFieldVariableLift_isFractionRing_toFracY
-- name    : ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.isFractionRing_toFracY
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:33.773116+00:00
-- url     : https://prove2.me/theorems/39442c53-0efe-46ae-9565-f15bb4565005
-- title:
--   Fraction Field Variable Lift: is Fraction Ring to Frac Y
-- statement:
--   The Fraction Field Variable Lift construction uses the is Fraction Ring to Frac Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteDimensionalOfLiftY.lean#L45-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteDimensionalOfLiftY.lean#L45-L76

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
set_option synthInstance.maxHeartbeats 400000

theorem ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.isFractionRing_toFracY :
    letI := (toFracY A σ).toAlgebra
    IsFractionRing (MvPolynomial σ A) (FractionRing (MvPolynomial σ (FractionRing A))) := by sorry
