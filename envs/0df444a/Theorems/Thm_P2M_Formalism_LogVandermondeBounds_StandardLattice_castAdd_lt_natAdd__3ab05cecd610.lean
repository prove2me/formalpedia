-- Prove2me | Theorems.Thm_P2M_Formalism_LogVandermondeBounds_StandardLattice_castAdd_lt_natAdd__3ab05cecd610
-- name    : P2M_Formalism_LogVandermondeBounds_StandardLattice_castAdd_lt_natAdd__3ab05cecd610
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:58:50.375545+00:00
-- url     : https://prove2.me/theorems/6c2bb615-a875-43e1-97c2-f29756f36473
-- title:
--   P2 M Formalism Log Vandermonde Bounds Standard Lattice cast Add lt nat Add  3ab05cecd610: P2 M Formalism Log Vandermonde Bounds Standard Lattice cast Add lt nat Add  3ab05cecd610
-- statement:
--   The P2 M Formalism Log Vandermonde Bounds Standard Lattice cast Add lt nat Add  3ab05cecd610 construction uses the P2 M Formalism Log Vandermonde Bounds Standard Lattice cast Add lt nat Add  3ab05cecd610 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/BlockDimensionIdentities.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/BlockDimensionIdentities.lean#L98-L102

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

theorem P2M_Formalism_LogVandermondeBounds_StandardLattice_castAdd_lt_natAdd__3ab05cecd610 {a m : ℕ} (i : Fin a) (j : Fin m) :
    Fin.castAdd m i < Fin.natAdd a j := by sorry

alias «Formalism».«LogVandermondeBounds».«StandardLattice».«castAdd_lt_natAdd'» := P2M_Formalism_LogVandermondeBounds_StandardLattice_castAdd_lt_natAdd__3ab05cecd610
