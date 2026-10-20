-- Prove2me | Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_sum_boundary_transportedUnivFinpartition
-- name    : SoficGroups.KunTransportedAmbientOverlap.sum_boundary_transportedUnivFinpartition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/747b9560-8aaa-4d5c-a0b4-a3a133cbac23
-- title:
--   SoficGroups.KunTransportedAmbientOverlap.sum_boundary_transportedUnivFinpartition
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

theorem SoficGroups.KunTransportedAmbientOverlap.sum_boundary_transportedUnivFinpartition
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V) (T : Equiv.Perm V) :
    (∑ C ∈ (SoficGroups.transportedUnivFinpartition Q T).parts,
      SoficGroups.boundary
        (fun i => T * σ i * T⁻¹) C) =
      ∑ C ∈ Q.parts, SoficGroups.boundary σ C := by sorry
