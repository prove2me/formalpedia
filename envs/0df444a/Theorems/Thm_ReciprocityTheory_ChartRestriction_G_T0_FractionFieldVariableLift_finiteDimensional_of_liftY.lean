-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FractionFieldVariableLift_finiteDimensional_of_liftY
-- name    : ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.finiteDimensional_of_liftY
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:58.389701+00:00
-- url     : https://prove2.me/theorems/6adb0b9c-25bf-51e7-aaea-912f916b7bad
-- title:
--   Fraction Field Variable Lift: finite Dimensional of lift Y
-- statement:
--   The Fraction Field Variable Lift construction uses the finite Dimensional of lift Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteDimensionalOfLiftY.lean#L144-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteDimensionalOfLiftY.lean#L144-L158

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
variable {L E : Type} [Field L] [Field E] [Algebra L E] {σ : Type}

theorem ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.finiteDimensional_of_liftY
    (hfin : letI := (VariableBasisExtension.liftY (L := L) (E := E) (σ := σ)).toAlgebra
      FiniteDimensional (FractionRing (MvPolynomial σ L)) (FractionRing (MvPolynomial σ E))) :
    FiniteDimensional L E := by sorry
