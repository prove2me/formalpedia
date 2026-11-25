-- Prove2me | Theorems.Thm_P2M_Formalism_LogVandermondeBounds_StandardLattice_not_natAdd_lt_castAdd__c751723af974
-- name    : P2M_Formalism_LogVandermondeBounds_StandardLattice_not_natAdd_lt_castAdd__c751723af974
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:21.780851+00:00
-- url     : https://prove2.me/theorems/04a9f057-9bd0-4b21-baa6-f1bf3d53151c
-- title:
--   P2 M Formalism Log Vandermonde Bounds Standard Lattice not nat Add lt cast Add  c751723af974: P2 M Formalism Log Vandermonde Bounds Standard Lattice not nat Add lt cast Add  c751723af974
-- statement:
--   The P2 M Formalism Log Vandermonde Bounds Standard Lattice not nat Add lt cast Add  c751723af974 construction uses the P2 M Formalism Log Vandermonde Bounds Standard Lattice not nat Add lt cast Add  c751723af974 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/BlockDimensionIdentities.lean#L104-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/BlockDimensionIdentities.lean#L104-L108

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

theorem P2M_Formalism_LogVandermondeBounds_StandardLattice_not_natAdd_lt_castAdd__c751723af974 {a m : ℕ} (i : Fin m) (j : Fin a) :
    ¬ Fin.natAdd a i < Fin.castAdd m j := by sorry

alias «Formalism».«LogVandermondeBounds».«StandardLattice».«not_natAdd_lt_castAdd'» := P2M_Formalism_LogVandermondeBounds_StandardLattice_not_natAdd_lt_castAdd__c751723af974
