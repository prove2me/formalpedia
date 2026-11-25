-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SecLift_mem_of_flat__d784d2797ad4
-- name    : P2M_GlobalTheory_SecLift_mem_of_flat__d784d2797ad4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:10:07.44257+00:00
-- url     : https://prove2.me/theorems/364a4aeb-1202-495d-8ad6-d1fa7468d3da
-- title:
--   P2 M Global Theory Sec Lift mem of flat  d784d2797ad4: P2 M Global Theory Sec Lift mem of flat  d784d2797ad4
-- statement:
--   The P2 M Global Theory Sec Lift mem of flat  d784d2797ad4 construction uses the P2 M Global Theory Sec Lift mem of flat  d784d2797ad4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecLift.lean#L68-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecLift.lean#L68-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]

theorem P2M_GlobalTheory_SecLift_mem_of_flat__d784d2797ad4 {a : A} {I : Ideal A} (hI : ∀ x, a * x = 0 → x ∈ I) {B : Type} [CommRing B]
    (c : A →+* B) (hf : c.Flat) (b : B) (hb : c a * b = 0) : b ∈ I.map c := by sorry

alias «GlobalTheory».«SecLift».«mem_of_flat'» := P2M_GlobalTheory_SecLift_mem_of_flat__d784d2797ad4
