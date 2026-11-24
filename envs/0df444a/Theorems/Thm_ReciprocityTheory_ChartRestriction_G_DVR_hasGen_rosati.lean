-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasGen_rosati
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.hasGen_rosati
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:09.425244+00:00
-- url     : https://prove2.me/theorems/2950b9a8-6f3d-4789-b652-e91665e8ef89
-- title:
--   DVR: has Gen rosati
-- statement:
--   The DVR construction uses the has Gen rosati property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L197-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L197-L224

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.hasGen_rosati (f g : A ⟶ A)
    (u : LB.Gen (LB.LinComb M (Out.rosatiφ A f g) Out.rosatiε)) (hu : u.IsGen) (x z : T ⟶ A) :
    HasGen M (lf (lamP (x ≫ f) z - lamP x (z ≫ g))) := by sorry
