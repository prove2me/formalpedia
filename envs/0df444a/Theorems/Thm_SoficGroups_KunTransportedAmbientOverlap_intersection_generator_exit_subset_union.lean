-- Prove2me | Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_intersection_generator_exit_subset_union
-- name    : SoficGroups.KunTransportedAmbientOverlap.intersection_generator_exit_subset_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/e46ecae7-6e97-4503-a063-e31537e37ab1
-- title:
--   SoficGroups.KunTransportedAmbientOverlap.intersection_generator_exit_subset_union
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

theorem SoficGroups.KunTransportedAmbientOverlap.intersection_generator_exit_subset_union
    {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (C D : Finset V) :
    ((C ∩ D).filter fun x => p x ∉ C ∩ D) ⊆
      ((C.filter fun x => p x ∉ C) ∩ D) ∪
        ((D.filter fun x => p x ∉ D) ∩ C) := by sorry
