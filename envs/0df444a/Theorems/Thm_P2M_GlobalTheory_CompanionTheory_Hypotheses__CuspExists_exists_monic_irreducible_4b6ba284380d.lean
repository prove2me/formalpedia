-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_exists_monic_irreducible_4b6ba284380d
-- name    : P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_exists_monic_irreducible_4b6ba284380d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T04:39:18.569314+00:00
-- url     : https://prove2.me/theorems/607fda21-ba86-5581-8b8c-d93f9d632736
-- title:
--   P2 M Global Theory Companion Theory Hypotheses  Cusp Exists exists monic irreducible 4b6ba284380d: P2 M Global Theory Companion Theory Hypotheses  Cusp Exists exists monic irreducible 4b6ba284380d
-- statement:
--   The P2 M Global Theory Companion Theory Hypotheses  Cusp Exists exists monic irreducible 4b6ba284380d construction uses the P2 M Global Theory Companion Theory Hypotheses  Cusp Exists exists monic irreducible 4b6ba284380d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L89-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/IsIrreducibleTransportRep.lean#L89-L107

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

theorem P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_exists_monic_irreducible_4b6ba284380d (d : ℕ) (hd : 1 ≤ d) :
    ∃ P : K[X], P.Monic ∧ Irreducible P ∧ P ≠ X ∧ P.natDegree = d := by sorry

alias «GlobalTheory».«CompanionTheory».«Hypotheses₂».«CuspExists».«exists_monic_irreducible» := P2M_GlobalTheory_CompanionTheory_Hypotheses__CuspExists_exists_monic_irreducible_4b6ba284380d
