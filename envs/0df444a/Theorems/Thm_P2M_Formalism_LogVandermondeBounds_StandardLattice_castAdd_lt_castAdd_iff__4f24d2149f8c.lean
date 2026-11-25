-- Prove2me | Theorems.Thm_P2M_Formalism_LogVandermondeBounds_StandardLattice_castAdd_lt_castAdd_iff__4f24d2149f8c
-- name    : P2M_Formalism_LogVandermondeBounds_StandardLattice_castAdd_lt_castAdd_iff__4f24d2149f8c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:58:38.914614+00:00
-- url     : https://prove2.me/theorems/f7859b75-c955-4738-913e-96b3d58b7129
-- title:
--   P2 M Formalism Log Vandermonde Bounds Standard Lattice cast Add lt cast Add iff  4f24d2149f8c: P2 M Formalism Log Vandermonde Bounds Standard Lattice cast Add lt cast Add iff  4f24d2149f8c
-- statement:
--   The P2 M Formalism Log Vandermonde Bounds Standard Lattice cast Add lt cast Add iff  4f24d2149f8c construction uses the P2 M Formalism Log Vandermonde Bounds Standard Lattice cast Add lt cast Add iff  4f24d2149f8c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/BlockDimensionIdentities.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/BlockDimensionIdentities.lean#L94-L96

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_BlockDimensionIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset

theorem P2M_Formalism_LogVandermondeBounds_StandardLattice_castAdd_lt_castAdd_iff__4f24d2149f8c {a m : ℕ} (i j : Fin a) :
    Fin.castAdd m i < Fin.castAdd m j ↔ i < j := by sorry

alias «Formalism».«LogVandermondeBounds».«StandardLattice».«castAdd_lt_castAdd_iff'» := P2M_Formalism_LogVandermondeBounds_StandardLattice_castAdd_lt_castAdd_iff__4f24d2149f8c
