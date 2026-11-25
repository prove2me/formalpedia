-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_smooth_free_away__350d1efab22d
-- name    : P2M_GlobalTheory_T_exists_smooth_free_away__350d1efab22d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:09:59.227998+00:00
-- url     : https://prove2.me/theorems/aa3b8adc-6332-4406-b783-c8843d2d4953
-- title:
--   P2 M Global Theory T exists smooth free away  350d1efab22d: P2 M Global Theory T exists smooth free away  350d1efab22d
-- statement:
--   The P2 M Global Theory T exists smooth free away  350d1efab22d construction uses the P2 M Global Theory T exists smooth free away  350d1efab22d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothFreeAwayStatement.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSmoothFreeAwayStatement.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothFreeAwayStatement
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

theorem P2M_GlobalTheory_T_exists_smooth_free_away__350d1efab22d : ∀ (k C : Type) [Field k] [PerfectField k] [CommRing C] [Nontrivial C] [IsReduced C] [Algebra k C] [Algebra.FiniteType k C] (M : Type) [AddCommGroup M] [Module C M] [Module.Finite C M], ∃ f : C, f ≠ 0 ∧ Algebra.Smooth k (Localization.Away f) ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by sorry

alias «GlobalTheory».«T».«exists_smooth_free_away'» := P2M_GlobalTheory_T_exists_smooth_free_away__350d1efab22d
