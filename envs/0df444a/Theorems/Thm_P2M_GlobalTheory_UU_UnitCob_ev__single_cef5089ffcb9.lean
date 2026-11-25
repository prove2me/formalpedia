-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UU_UnitCob_ev__single_cef5089ffcb9
-- name    : P2M_GlobalTheory_UU_UnitCob_ev__single_cef5089ffcb9
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T16:42:08.874219+00:00
-- url     : https://prove2.me/theorems/76372c3c-c6ab-569d-8b46-84bda579252e
-- title:
--   P2 M Global Theory UU Unit Cob ev  single cef5089ffcb9: P2 M Global Theory UU Unit Cob ev  single cef5089ffcb9
-- statement:
--   The P2 M Global Theory UU Unit Cob ev  single cef5089ffcb9 construction uses the P2 M Global Theory UU Unit Cob ev  single cef5089ffcb9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CoeffMemOfPoints.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CoeffMemOfPoints.lean#L87-L89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompRedIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitCoboundaryOfMulCocycleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CoeffMemOfPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.UU.RingPoint
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.UnitCob
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}

theorem P2M_GlobalTheory_UU_UnitCob_ev__single_cef5089ffcb9 {Z : Over S} (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (m : X × X) (b) :
    ev₂ t t' y (AddMonoidAlgebra.single m b) = y.left.appTop.hom b * ((chV t m.1).val * (chV t' m.2).val) := by sorry

alias «GlobalTheory».«UU».«UnitCob».«ev₂_single» := P2M_GlobalTheory_UU_UnitCob_ev__single_cef5089ffcb9
