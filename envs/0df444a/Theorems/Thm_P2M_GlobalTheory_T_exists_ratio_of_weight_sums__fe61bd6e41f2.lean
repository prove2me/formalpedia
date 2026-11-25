-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_ratio_of_weight_sums__fe61bd6e41f2
-- name    : P2M_GlobalTheory_T_exists_ratio_of_weight_sums__fe61bd6e41f2
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:14:59.680106+00:00
-- url     : https://prove2.me/theorems/30d59b29-3604-5735-9d8b-a718a9a3e3d0
-- title:
--   P2 M Global Theory T exists ratio of weight sums  fe61bd6e41f2: P2 M Global Theory T exists ratio of weight sums  fe61bd6e41f2
-- statement:
--   The P2 M Global Theory T exists ratio of weight sums  fe61bd6e41f2 construction uses the P2 M Global Theory T exists ratio of weight sums  fe61bd6e41f2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRatioOfWeightSumsStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsRatioOfWeightSumsStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSums
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSumsStatement
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

theorem P2M_GlobalTheory_T_exists_ratio_of_weight_sums__fe61bd6e41f2 : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → ∀ (U : G.left.Opens) (f : Γ(G.left, U)), (U : Set G.left).Nonempty → ∃ (U' : G.left.Opens) (h : U' ≤ U) (n : ℕ) (a b : Fin n → Γ(G.left, U')) (χ : Fin n → X), (U' : Set G.left).Nonempty ∧ (∀ j, Wt i U' (a j) (χ j) ∧ Wt i U' (b j) (χ j) ∧ (a j = 0 ∨ IsUnit (a j)) ∧ (b j = 0 ∨ IsUnit (b j))) ∧ IsUnit (∑ j, b j) ∧ (G.left.presheaf.map (homOfLE h).op).hom f * ∑ j, b j = ∑ j, a j := by sorry

alias «GlobalTheory».«T».«exists_ratio_of_weight_sums'» := P2M_GlobalTheory_T_exists_ratio_of_weight_sums__fe61bd6e41f2
