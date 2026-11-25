-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_act_zero__09a1d8b138bd
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_act_zero__09a1d8b138bd
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:00.23271+00:00
-- url     : https://prove2.me/theorems/15b4a32a-e241-4ca3-934b-fa85a4f3918e
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR act zero  09a1d8b138bd: P2 M Reciprocity Theory Chart Restriction G DVR act zero  09a1d8b138bd
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR act zero  09a1d8b138bd construction uses the P2 M Reciprocity Theory Chart Restriction G DVR act zero  09a1d8b138bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L232-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/CartesianLiftThreeCompProjection.lean#L232-L235

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_act_zero__09a1d8b138bd (ra : Out.RingAct A O) : ra.act 0 = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«act_zero'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_act_zero__09a1d8b138bd
