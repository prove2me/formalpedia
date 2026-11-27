-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_QForm_rosati__over_86818d940d9f
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_QForm_rosati__over_86818d940d9f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T06:20:50.142221+00:00
-- url     : https://prove2.me/theorems/758b6b31-19db-572d-ad0b-aa7719fc6a1c
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR QForm rosati  over 86818d940d9f: P2 M Reciprocity Theory Chart Restriction G DVR QForm rosati  over 86818d940d9f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR QForm rosati  over 86818d940d9f construction uses the P2 M Reciprocity Theory Chart Restriction G DVR QForm rosati  over 86818d940d9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsRosatiGen.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsRosatiGen.lean#L47-L51

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsRosatiGen
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
  (D : DegData V (maximalIdeal V))
variable {Q : D.toPre.X → ℤ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_QForm_rosati__over_86818d940d9f {S : Scheme.{0}} (A : Over S) [GrpObj A] (f g : A ⟶ A) (k : Fin 6) :
    ∃ q : A ⊗ A ⟶ A, rosatiφ A f g k = q.left := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«QForm».«rosatiφ_over» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_QForm_rosati__over_86818d940d9f
