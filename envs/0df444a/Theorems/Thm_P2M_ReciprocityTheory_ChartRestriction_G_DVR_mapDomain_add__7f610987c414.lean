-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_mapDomain_add__7f610987c414
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_mapDomain_add__7f610987c414
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:48.369802+00:00
-- url     : https://prove2.me/theorems/5b6300dd-6df4-4a82-8e8d-c34bec674d65
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR map Domain add  7f610987c414: P2 M Reciprocity Theory Chart Restriction G DVR map Domain add  7f610987c414
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR map Domain add  7f610987c414 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR map Domain add  7f610987c414 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L144-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L144-L146

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_mapDomain_add__7f610987c414 {α β : Type} (f : α → β) (F G : α →₀ ℤ) :
    Finsupp.mapDomain f (F + G) = Finsupp.mapDomain f F + Finsupp.mapDomain f G := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«mapDomain_add'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_mapDomain_add__7f610987c414
