-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UU_UnitCob_appTop_ev__8715276f39bc
-- name    : P2M_GlobalTheory_UU_UnitCob_appTop_ev__8715276f39bc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T16:44:38.450782+00:00
-- url     : https://prove2.me/theorems/01452412-2110-51a8-b2fb-8af415680170
-- title:
--   P2 M Global Theory UU Unit Cob app Top ev  8715276f39bc: P2 M Global Theory UU Unit Cob app Top ev  8715276f39bc
-- statement:
--   The P2 M Global Theory UU Unit Cob app Top ev  8715276f39bc construction uses the P2 M Global Theory UU Unit Cob app Top ev  8715276f39bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CoeffMemOfPoints.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CoeffMemOfPoints.lean#L118-L122

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

theorem P2M_GlobalTheory_UU_UnitCob_appTop_ev__8715276f39bc {Z : Over S} (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y) (a : AddMonoidAlgebra Γ(Y.left, ⊤) X) :
    (lift t y).left.appTop.hom (ev₁ (fst (splitTorus S X) Y) (snd _ _) a) = ev₁ t y a := by sorry

alias «GlobalTheory».«UU».«UnitCob».«appTop_ev₁» := P2M_GlobalTheory_UU_UnitCob_appTop_ev__8715276f39bc
