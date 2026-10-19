-- Prove2me | Theorems.Thm_SoficGroups_partitionWordCrossing_card_le_target_add_unmatched
-- name    : SoficGroups.partitionWordCrossing_card_le_target_add_unmatched
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/ab811e19-ed21-4d2a-8f35-644f45eec38f
-- title:
--   SoficGroups.partitionWordCrossing_card_le_target_add_unmatched
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff

theorem SoficGroups.partitionWordCrossing_card_le_target_add_unmatched
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P Q : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V)
    (hD : ∀ C ∈ R, D C ∈ Q.parts)
    (hinj : Set.InjOn D (R : Set (Finset V)))
    (w : Equiv.Perm V) :
    (partitionWordCrossing P w).card ≤
      (partitionWordCrossing Q w).card +
        2 * (U \ matchedCore R D).card := by sorry
