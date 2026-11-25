-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasGen_pullMul
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.hasGen_pullMul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:02.771352+00:00
-- url     : https://prove2.me/theorems/e781daf1-c402-40d5-9796-2cd585b4a2a7
-- title:
--   DVR: has Gen pull Mul
-- statement:
--   The DVR construction uses the has Gen pull Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L241-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L241-L270

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
variable {O : Type} [CommRing O] [StarRing O]

theorem ReciprocityTheory.ChartRestriction.G.DVR.hasGen_pullMul (ra : Out.RingAct A O) (w0 a : O) (N : ℕ) (hN : a * star a = (N : O))
    (uΨ : LB.Gen (LB.LinComb M (K := Fin 4)
      ![(padd A (𝟙 _) (ra.act w0)).left, 𝟙 A.left, (ra.act w0).left, (toUnit A ≫ η[A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen)
    (uR : LB.Gen (LB.LinComb M (Out.rosatiφ A (ra.act a) (ra.act (star a))) Out.rosatiε)) (huR : uR.IsGen)
    (t : LB.Gen (Theta A M)) (ht : t.IsGen) :
    HasGen M (lf (Finsupp.single (ra.act a) 1 - (N : ℤ) • Finsupp.single (𝟙 A) 1 +
      ((N : ℤ) - 1) • Finsupp.single (1 : A ⟶ A) 1)) := by sorry
