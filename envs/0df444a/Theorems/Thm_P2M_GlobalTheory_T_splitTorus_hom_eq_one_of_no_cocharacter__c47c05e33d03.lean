-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_splitTorus_hom_eq_one_of_no_cocharacter__c47c05e33d03
-- name    : P2M_GlobalTheory_T_splitTorus_hom_eq_one_of_no_cocharacter__c47c05e33d03
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:23.483065+00:00
-- url     : https://prove2.me/theorems/6c385239-0729-4315-8880-b44e39ff9abb
-- title:
--   P2 M Global Theory T split Torus hom eq one of no cocharacter  c47c05e33d03: P2 M Global Theory T split Torus hom eq one of no cocharacter  c47c05e33d03
-- statement:
--   The P2 M Global Theory T split Torus hom eq one of no cocharacter  c47c05e33d03 construction uses the P2 M Global Theory T split Torus hom eq one of no cocharacter  c47c05e33d03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusHomEqOneOfNoCocharacterStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusHomEqOneOfNoCocharacterStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusHomEqOneOfNoCocharacter
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusHomEqOneOfNoCocharacterStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_splitTorus_hom_eq_one_of_no_cocharacter__c47c05e33d03 : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], (∀ f : Gm S ⟶ B, IsMonHom f → f = 1) → ∀ u : splitTorus S X ⟶ B, IsMonHom u → u = 1 := by sorry

alias «GlobalTheory».«T».«splitTorus_hom_eq_one_of_no_cocharacter'» := P2M_GlobalTheory_T_splitTorus_hom_eq_one_of_no_cocharacter__c47c05e33d03
