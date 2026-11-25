-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasGen_lam_pow
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.hasGen_lam_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:15.352514+00:00
-- url     : https://prove2.me/theorems/475babca-537f-5a66-92e2-1db397b2b1b9
-- title:
--   DVR: has Gen lam pow
-- statement:
--   The DVR construction uses the has Gen lam pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L129-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L129-L138

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S}
variable {M : LB A.left}

theorem ReciprocityTheory.ChartRestriction.G.DVR.hasGen_lam_pow (t : LB.Gen (Theta A M)) (ht : t.IsGen) (x y : T ⟶ A) :
    ∀ n : ℕ, HasGen M (lf (lamP x (y ^ n) - (n : ℤ) • lamP x y))
  := by sorry
