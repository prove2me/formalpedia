-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_tower_le_eb30067214cf
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_tower_le_eb30067214cf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T04:39:43.895111+00:00
-- url     : https://prove2.me/theorems/734017da-fc84-5854-9324-e712c2f31d39
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Cusp Exists tower le eb30067214cf: P2 M Global Theory Companion Theory Hypotheses  Cusp Exists tower le eb30067214cf
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Cusp Exists tower le eb30067214cf construction uses the P2 M Global Theory Companion Theory Hypotheses  Cusp Exists tower le eb30067214cf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L62-L68

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_tower_le_eb30067214cf {k l : ℕ} (h : k ≤ l) :
    (tower K l).1 ^ ((Fintype.card K ^ l.factorial - 1) / (Fintype.card K ^ k.factorial - 1)) = (tower K k).1 := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CuspExists».«tower_le» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_tower_le_eb30067214cf
