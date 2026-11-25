-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_theta
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.fsum_theta
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:11:38.750136+00:00
-- url     : https://prove2.me/theorems/f0753f86-99f0-4cb0-a715-2f74e94cea56
-- title:
--   DVR: fsum theta
-- statement:
--   The DVR construction uses the fsum theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L72-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L72-L103

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.fsum_theta (x y z : T ⟶ A) :
    fsum (fun I : ULift.{0} (Finset (Fin 3)) => (psum A ![x, y, z] I.down).left)
        (fun I => (-1 : ℤ) ^ (3 - I.down.card)) =
      lf (lamP x (y * z) - lamP x y - lamP x z) := by sorry
