-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_isCuspidal_transportRep_37b7509b08da
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_isCuspidal_transportRep_37b7509b08da
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T04:42:22.348978+00:00
-- url     : https://prove2.me/theorems/62f7ba94-8dab-5a8b-9275-37b23594caef
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Cusp Exists is Cuspidal transport Rep 37b7509b08da: P2 M Global Theory Companion Theory Hypotheses  Cusp Exists is Cuspidal transport Rep 37b7509b08da
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Cusp Exists is Cuspidal transport Rep 37b7509b08da construction uses the P2 M Global Theory Companion Theory Hypotheses  Cusp Exists is Cuspidal transport Rep 37b7509b08da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L148-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L148-L174

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_isCuspidal_transportRep_37b7509b08da {K : Type} [Field K] [Fintype K] [DecidableEq K] {N : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (τ : FDRep ℂ (GL (Fin N) K)) (h : Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ) (e : τ ≃ₗ[ℂ] W) :
    GlobalTheory.FiniteGL.IsCuspidal (transportRep τ.ρ e) := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CuspExists».«isCuspidal_transportRep» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_isCuspidal_transportRep_37b7509b08da
