-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_tower_succ_0f3880c54c8e
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_tower_succ_0f3880c54c8e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T04:39:39.882389+00:00
-- url     : https://prove2.me/theorems/e7a744b7-e063-5115-b1be-f017cbdfe4e6
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Cusp Exists tower succ 0f3880c54c8e: P2 M Global Theory Companion Theory Hypotheses  Cusp Exists tower succ 0f3880c54c8e
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Cusp Exists tower succ 0f3880c54c8e construction uses the P2 M Global Theory Companion Theory Hypotheses  Cusp Exists tower succ 0f3880c54c8e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L55-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L55-L60

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_tower_succ_0f3880c54c8e (k : ℕ) :
    (tower K (k + 1)).1 ^ ((Fintype.card K ^ (k + 1).factorial - 1) / (Fintype.card K ^ k.factorial - 1)) =
      (tower K k).1 := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CuspExists».«tower_succ» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_tower_succ_0f3880c54c8e
