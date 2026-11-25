-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_poly_normSq_roots__42597430cd16
-- name    : P2M_GlobalTheory_T_exists_poly_normSq_roots__42597430cd16
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:53:35.458801+00:00
-- url     : https://prove2.me/theorems/3f75c495-220c-46c8-8281-5b9f4733d298
-- title:
--   P2 M Global Theory T exists poly norm Sq roots  42597430cd16: P2 M Global Theory T exists poly norm Sq roots  42597430cd16
-- statement:
--   The P2 M Global Theory T exists poly norm Sq roots  42597430cd16 construction uses the P2 M Global Theory T exists poly norm Sq roots  42597430cd16 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPolyNormSqRootsStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPolyNormSqRootsStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPolyNormSqRoots
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPolyNormSqRootsStatement
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

theorem P2M_GlobalTheory_T_exists_poly_normSq_roots__42597430cd16 : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B → ∀ (L : LB B.left), AmpleCub B L → ∀ (F : End B) (q : ℕ), IsMonHom (show B ⟶ B from F) → PullPow (show B ⟶ B from F).left L q → ∃ P : Polynomial ℤ, P ≠ 0 ∧ (∀ β : ℂ, Polynomial.aeval β P = 0 → Complex.normSq β = q) ∧ ∀ x : (𝟙_ (Over (Sp k)) ⟶ B), polyPt F P x = 1 := by sorry

alias «GlobalTheory».«T».«exists_poly_normSq_roots'» := P2M_GlobalTheory_T_exists_poly_normSq_roots__42597430cd16
