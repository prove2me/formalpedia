-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_exists_genSys_61c6f4b2c08c
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_exists_genSys_61c6f4b2c08c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-27T04:39:38.610379+00:00
-- url     : https://prove2.me/theorems/8db28b4d-fd18-59b0-b988-a56fa5254a5a
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Cusp Exists exists gen Sys 61c6f4b2c08c: P2 M Global Theory Companion Theory Hypotheses  Cusp Exists exists gen Sys 61c6f4b2c08c
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Cusp Exists exists gen Sys 61c6f4b2c08c construction uses the P2 M Global Theory Companion Theory Hypotheses  Cusp Exists exists gen Sys 61c6f4b2c08c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L70-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L70-L81

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
variable (K : Type) [Field K] [Fintype K]

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_exists_genSys_61c6f4b2c08c : ∃ ζ : ℕ → AlgebraicClosure K, ∀ d, 0 < d → orderOf (ζ d) = Fintype.card K ^ d - 1 ∧
    ∀ d', d ∣ d' → 0 < d' → ζ d' ^ ((Fintype.card K ^ d' - 1) / (Fintype.card K ^ d - 1)) = ζ d := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CuspExists».«exists_genSys» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_exists_genSys_61c6f4b2c08c
