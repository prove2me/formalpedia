-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasGen_psi
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.hasGen_psi
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:11:07.816051+00:00
-- url     : https://prove2.me/theorems/a8d75bd7-8d76-5c9f-bd05-9bc56f59b921
-- title:
--   DVR: has Gen psi
-- statement:
--   The DVR construction uses the has Gen psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L173-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L173-L195

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.hasGen_psi (w : A ⟶ A)
    (u : LB.Gen (LB.LinComb M (K := Fin 4)
      ![(padd A (𝟙 _) w).left, 𝟙 A.left, w.left, (toUnit A ≫ η[A]).left] ![1, -2, -1, 2]))
    (hu : u.IsGen) (y : T ⟶ A) : HasGen M (lf (psiP w y)) := by sorry
