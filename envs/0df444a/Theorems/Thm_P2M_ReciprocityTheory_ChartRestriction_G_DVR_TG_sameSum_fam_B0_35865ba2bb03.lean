-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_sameSum_fam_B0_35865ba2bb03
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_sameSum_fam_B0_35865ba2bb03
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:14:41.831882+00:00
-- url     : https://prove2.me/theorems/b4b23c8b-b406-469f-8fbe-4e87bc5006b1
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR TG same Sum fam B0 35865ba2bb03: P2 M Reciprocity Theory Chart Restriction G DVR TG same Sum fam B0 35865ba2bb03
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR TG same Sum fam B0 35865ba2bb03 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR TG same Sum fam B0 35865ba2bb03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenRank.lean#L189-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenRank.lean#L189-L206

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_sameSum_fam_B0_35865ba2bb03 : LB.SameSum (D.toPre.famφB 0) (DegPre.famε 1)
    (fun _ : Fin 1 => 𝟙 D.toPre.P.A.left) (fun _ => ((1 : ℕ) : ℤ)) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«TG».«sameSum_famφB0» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_TG_sameSum_fam_B0_35865ba2bb03
