-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FractionFieldVariableLift_clear_denoms
-- name    : ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.clear_denoms
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:59.547488+00:00
-- url     : https://prove2.me/theorems/d897ea66-8c46-5e8e-9203-d418a3dbaf0b
-- title:
--   Fraction Field Variable Lift: clear denoms
-- statement:
--   The Fraction Field Variable Lift construction uses the clear denoms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteDimensionalOfLiftY.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/FiniteDimensionalOfLiftY.lean#L11-L28

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

theorem ReciprocityTheory.ChartRestriction.G.T0.FractionFieldVariableLift.clear_denoms (P : MvPolynomial σ (FractionRing A)) :
    ∃ (b : A) (p : MvPolynomial σ A), b ≠ 0 ∧
      MvPolynomial.map (algebraMap A (FractionRing A)) p =
        MvPolynomial.C (algebraMap A (FractionRing A) b) * P := by sorry
