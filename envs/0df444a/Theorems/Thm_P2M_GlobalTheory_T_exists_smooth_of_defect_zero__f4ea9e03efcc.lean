-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_smooth_of_defect_zero__f4ea9e03efcc
-- name    : P2M_GlobalTheory_T_exists_smooth_of_defect_zero__f4ea9e03efcc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:25.850746+00:00
-- url     : https://prove2.me/theorems/dbbec229-f888-4b80-a399-ad881e1260f6
-- title:
--   P2 M Global Theory T exists smooth of defect zero  f4ea9e03efcc: P2 M Global Theory T exists smooth of defect zero  f4ea9e03efcc
-- statement:
--   The P2 M Global Theory T exists smooth of defect zero  f4ea9e03efcc construction uses the P2 M Global Theory T exists smooth of defect zero  f4ea9e03efcc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZeroStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothOfDefectZeroStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZeroStatement
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

theorem P2M_GlobalTheory_T_exists_smooth_of_defect_zero__f4ea9e03efcc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R), Irreducible π → ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] [Module.Flat R B], Algebra.Smooth R (Localization.Away (algebraMap R B π)) → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (a : B →ₐ[R] R'), Unr π R' → Defect a π 0 → ∃ f : B, IsUnit (a f) ∧ Algebra.Smooth R (Localization.Away f) := by sorry

alias «GlobalTheory».«T».«exists_smooth_of_defect_zero'» := P2M_GlobalTheory_T_exists_smooth_of_defect_zero__f4ea9e03efcc
