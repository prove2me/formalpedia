-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_transportRep_apply_3ef9cc1a238f
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_transportRep_apply_3ef9cc1a238f
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T04:44:52.629831+00:00
-- url     : https://prove2.me/theorems/3dcd63fd-1e4d-4535-b020-2b758af34604
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Cusp Exists transport Rep apply 3ef9cc1a238f: P2 M Global Theory Companion Theory Hypotheses  Cusp Exists transport Rep apply 3ef9cc1a238f
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Cusp Exists transport Rep apply 3ef9cc1a238f construction uses the P2 M Global Theory Companion Theory Hypotheses  Cusp Exists transport Rep apply 3ef9cc1a238f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L120-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L120-L121

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCuspidalWithLabel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsTeichmullerMapAlgebraicClosureFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIrreducibleTransportRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.CuspExists
variable {G V W : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_transportRep_apply_3ef9cc1a238f (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) (g : G) (w : W) :
    transportRep ρ e g w = e (ρ g (e.symm w)) := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CuspExists».«transportRep_apply» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_transportRep_apply_3ef9cc1a238f
