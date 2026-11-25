-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_fam_B0_one_2c33f401c32a
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_fam_B0_one_2c33f401c32a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:15:25.251442+00:00
-- url     : https://prove2.me/theorems/72513eb5-5ae8-5ff7-adcf-f43fa6af47a0
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR TG fam B0 one 2c33f401c32a: P2 M Reciprocity Theory Chart Restriction G DVR TG fam B0 one 2c33f401c32a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR TG fam B0 one 2c33f401c32a construction uses the P2 M Reciprocity Theory Chart Restriction G DVR TG fam B0 one 2c33f401c32a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenRank.lean#L168-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenRank.lean#L168-L180

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenRank
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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I)

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_fam_B0_one_2c33f401c32a : D.toPre.famφB 0 1 = 𝟙 _ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«TG».«famφB0_one» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_fam_B0_one_2c33f401c32a
