-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_integral_ext_isAlgClosed_residueField__26ccfe479fac
-- name    : P2M_GlobalTheory_T_exists_integral_ext_isAlgClosed_residueField__26ccfe479fac
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:08:26.304325+00:00
-- url     : https://prove2.me/theorems/c0dc7cfc-24ea-508d-8d47-16c5ac3bef69
-- title:
--   P2 M Global Theory T exists integral ext is Alg Closed residue Field  26ccfe479fac: P2 M Global Theory T exists integral ext is Alg Closed residue Field  26ccfe479fac
-- statement:
--   The P2 M Global Theory T exists integral ext is Alg Closed residue Field  26ccfe479fac construction uses the P2 M Global Theory T exists integral ext is Alg Closed residue Field  26ccfe479fac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIntegralExtIsAlgClosedResidueFieldStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIntegralExtIsAlgClosedResidueFieldStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIntegralExtIsAlgClosedResidueFieldStatement
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

theorem P2M_GlobalTheory_T_exists_integral_ext_isAlgClosed_residueField__26ccfe479fac : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W], ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (_ : Algebra W R), Function.Injective (algebraMap W R) ∧ Algebra.IsIntegral W R ∧ IsAlgClosed (IsLocalRing.ResidueField R) := by sorry

alias «GlobalTheory».«T».«exists_integral_ext_isAlgClosed_residueField'» := P2M_GlobalTheory_T_exists_integral_ext_isAlgClosed_residueField__26ccfe479fac
