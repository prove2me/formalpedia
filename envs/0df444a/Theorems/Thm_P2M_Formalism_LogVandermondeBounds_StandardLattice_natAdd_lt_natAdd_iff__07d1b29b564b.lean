-- Prove2me | Theorems.Thm_P2M_Formalism_LogVandermondeBounds_StandardLattice_natAdd_lt_natAdd_iff__07d1b29b564b
-- name    : P2M_Formalism_LogVandermondeBounds_StandardLattice_natAdd_lt_natAdd_iff__07d1b29b564b
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:58:45.536808+00:00
-- url     : https://prove2.me/theorems/9c1ca567-1cc7-4b64-9f04-1a70f3618c91
-- title:
--   P2 M Formalism Log Vandermonde Bounds Standard Lattice nat Add lt nat Add iff  07d1b29b564b: P2 M Formalism Log Vandermonde Bounds Standard Lattice nat Add lt nat Add iff  07d1b29b564b
-- statement:
--   The P2 M Formalism Log Vandermonde Bounds Standard Lattice nat Add lt nat Add iff  07d1b29b564b construction uses the P2 M Formalism Log Vandermonde Bounds Standard Lattice nat Add lt nat Add iff  07d1b29b564b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/BlockDimensionIdentities.lean#L110-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/BlockDimensionIdentities.lean#L110-L113

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

theorem P2M_Formalism_LogVandermondeBounds_StandardLattice_natAdd_lt_natAdd_iff__07d1b29b564b {a m : ℕ} (i j : Fin m) :
    Fin.natAdd a i < Fin.natAdd a j ↔ i < j := by sorry

alias «Formalism».«LogVandermondeBounds».«StandardLattice».«natAdd_lt_natAdd_iff'» := P2M_Formalism_LogVandermondeBounds_StandardLattice_natAdd_lt_natAdd_iff__07d1b29b564b
