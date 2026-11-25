-- Prove2me | Theorems.Thm_P2M_GlobalTheory_EquivDesc_lift_act__one_76b398679955
-- name    : P2M_GlobalTheory_EquivDesc_lift_act__one_76b398679955
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:35:57.897882+00:00
-- url     : https://prove2.me/theorems/b807ee9e-61f8-4c87-9165-2f9a8f60730d
-- title:
--   P2 M Global Theory Equiv Desc lift act  one 76b398679955: P2 M Global Theory Equiv Desc lift act  one 76b398679955
-- statement:
--   The P2 M Global Theory Equiv Desc lift act  one 76b398679955 construction uses the P2 M Global Theory Equiv Desc lift act  one 76b398679955 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsStalkHom.lean#L119-L121

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
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
open GlobalTheory.UU TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.EquivDesc
variable {S : Scheme.{0}}
variable {G H : Over S} [GrpObj G] [GrpObj H] {i : H ⟶ G} {L : LB G.left}

theorem P2M_GlobalTheory_EquivDesc_lift_act__one_76b398679955 {T : Over S} (t : T ⟶ H) (x : T ⟶ G) : (lift t x).left ≫ actφ i 1 = x.left := by sorry

alias «GlobalTheory».«EquivDesc».«lift_actφ_one» := P2M_GlobalTheory_EquivDesc_lift_act__one_76b398679955
