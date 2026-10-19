-- Prove2me | Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_sum_intersection_generator_exit_card_le
-- name    : SoficGroups.KunTransportedAmbientOverlap.sum_intersection_generator_exit_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/25e1ba68-d7a2-47d7-bd74-a63a7c06169e
-- title:
--   SoficGroups.KunTransportedAmbientOverlap.sum_intersection_generator_exit_card_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunTransportedAmbientOverlap
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.KunTransportedAmbientOverlap.sum_intersection_generator_exit_card_le
    {V : Type*} [DecidableEq V]
    {U : Finset V} (P Q : Finpartition U)
    (p : Equiv.Perm V) :
    (∑ C ∈ P.parts, ∑ D ∈ Q.parts,
      ((C ∩ D).filter fun x => p x ∉ C ∩ D).card) ≤
      (∑ C ∈ P.parts,
        (C.filter fun x => p x ∉ C).card) +
      (∑ D ∈ Q.parts,
        (D.filter fun x => p x ∉ D).card) := by sorry
