-- Prove2me | Theorems.Thm_SoficGroups_SourceRetainedActualMatching_retained_transport_component_matching_bounds
-- name    : SoficGroups.SourceRetainedActualMatching.retained_transport_component_matching_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/7f6ccaf7-9831-466a-9bb6-7b77a7a15959
-- title:
--   SoficGroups.SourceRetainedActualMatching.retained_transport_component_matching_bounds
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceRetainedActualMatching
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.SourceRetainedActualMatching.retained_transport_component_matching_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V)
    (H r eta : ℝ) (hH : 0 < H)
    (C : Finset V)
    (hC : C ∈ retainedTransportedComponents Q T H r eta) :
    SoficGroups.maximumOverlapPart Q C ∈ Q.parts ∧
      (1 - eta) * (C.card : ℝ) ≤
        ((C ∩ SoficGroups.maximumOverlapPart Q C).card : ℝ) ∧
      ((C ∆ SoficGroups.maximumOverlapPart Q C).card : ℝ) <
        (Real.exp H - 1 + 2 * eta) * (C.card : ℝ) ∧
      (2 * (Real.exp H - 1 + 2 * eta) < 1 →
        (SoficGroups.maximumOverlapPart Q C).card <
          2 * (C ∩ SoficGroups.maximumOverlapPart Q C).card) := by sorry
