-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_mapDomain_sub__7ba063a12c3d
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_mapDomain_sub__7ba063a12c3d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:31.902573+00:00
-- url     : https://prove2.me/theorems/b7deb811-12a5-4ff8-9d54-2c10edcf5435
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR map Domain sub  7ba063a12c3d: P2 M Reciprocity Theory Chart Restriction G DVR map Domain sub  7ba063a12c3d
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR map Domain sub  7ba063a12c3d construction uses the P2 M Reciprocity Theory Chart Restriction G DVR map Domain sub  7ba063a12c3d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L148-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L148-L150

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_mapDomain_sub__7ba063a12c3d {α β : Type} (f : α → β) (F G : α →₀ ℤ) :
    Finsupp.mapDomain f (F - G) = Finsupp.mapDomain f F - Finsupp.mapDomain f G := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«mapDomain_sub'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_mapDomain_sub__7ba063a12c3d
