-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_isIrreducible_transportRep_d83896ad2d55
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_isIrreducible_transportRep_d83896ad2d55
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T04:48:27.477591+00:00
-- url     : https://prove2.me/theorems/9b83788c-ebb6-4197-8ca7-089b948f82e4
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Cusp Exists is Irreducible transport Rep d83896ad2d55: P2 M Global Theory Companion Theory Hypotheses  Cusp Exists is Irreducible transport Rep d83896ad
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Cusp Exists is Irreducible transport Rep d83896ad2d55 construction uses the P2 M Global Theory Companion Theory Hypotheses  Cusp Exists is Irreducible transport Rep d83896ad2d55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L125-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L125-L146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsCuspidalWithLabel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsTeichmullerMapAlgebraicClosureFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IsIrreducibleTransportRep
import Theorems.Thm_GlobalTheory_BI_isIrreducible_transportRep

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_isIrreducible_transportRep_d83896ad2d55 {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ G V) (e : V ≃ₗ[ℂ] W) (hV : Nontrivial V)
    (h : ∀ U : Submodule ℂ V, (∀ g, ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤) : (transportRep ρ e).IsIrreducible := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CuspExists».«isIrreducible_transportRep» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_isIrreducible_transportRep_d83896ad2d55
