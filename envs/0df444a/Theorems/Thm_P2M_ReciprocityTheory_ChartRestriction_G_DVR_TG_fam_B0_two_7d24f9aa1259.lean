-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_fam_B0_two_7d24f9aa1259
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_fam_B0_two_7d24f9aa1259
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:55.69262+00:00
-- url     : https://prove2.me/theorems/90cddb05-3121-4dd4-94c1-6c20a0a10df3
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR TG fam B0 two 7d24f9aa1259: P2 M Reciprocity Theory Chart Restriction G DVR TG fam B0 two 7d24f9aa1259
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR TG fam B0 two 7d24f9aa1259 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR TG fam B0 two 7d24f9aa1259 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenRank.lean#L182-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenRank.lean#L182-L187

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_fam_B0_two_7d24f9aa1259 : D.toPre.famφB 0 2 = D.toPre.famφB 0 3 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«TG».«famφB0_two» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_fam_B0_two_7d24f9aa1259
