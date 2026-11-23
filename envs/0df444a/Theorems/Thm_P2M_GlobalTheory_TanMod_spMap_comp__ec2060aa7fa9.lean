-- Prove2me | Theorems.Thm_P2M_GlobalTheory_TanMod_spMap_comp__ec2060aa7fa9
-- name    : P2M_GlobalTheory_TanMod_spMap_comp__ec2060aa7fa9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:52.588799+00:00
-- url     : https://prove2.me/theorems/0fab62dd-5bdd-4923-9de2-4967c5a05cb5
-- title:
--   P2 M Global Theory Tan Mod sp Map comp  ec2060aa7fa9: P2 M Global Theory Tan Mod sp Map comp  ec2060aa7fa9
-- statement:
--   The P2 M Global Theory Tan Mod sp Map comp  ec2060aa7fa9 construction uses the P2 M Global Theory Tan Mod sp Map comp  ec2060aa7fa9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsTangentModuleUniversalGroup.lean#L169-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsTangentModuleUniversalGroup.lean#L169-L172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TanMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)
variable {G : Over X0} [GrpObj G]

theorem P2M_GlobalTheory_TanMod_spMap_comp__ec2060aa7fa9 {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by sorry

alias «GlobalTheory».«TanMod».«spMap_comp'» := P2M_GlobalTheory_TanMod_spMap_comp__ec2060aa7fa9
