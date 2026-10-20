-- Prove2me | Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_boundary_conjugate_map
-- name    : SoficGroups.KunTransportedAmbientOverlap.boundary_conjugate_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/52b64acb-b831-403d-b9af-231dc358fdff
-- title:
--   SoficGroups.KunTransportedAmbientOverlap.boundary_conjugate_map
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

theorem SoficGroups.KunTransportedAmbientOverlap.boundary_conjugate_map
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    (σ : ι → Equiv.Perm V) (T : Equiv.Perm V)
    (C : Finset V) :
    SoficGroups.boundary
      (fun i => T * σ i * T⁻¹)
      (C.map T.toEmbedding) =
        SoficGroups.boundary σ C := by sorry
