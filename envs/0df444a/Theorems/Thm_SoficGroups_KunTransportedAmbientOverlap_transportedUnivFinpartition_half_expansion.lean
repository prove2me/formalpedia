-- Prove2me | Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_transportedUnivFinpartition_half_expansion
-- name    : SoficGroups.KunTransportedAmbientOverlap.transportedUnivFinpartition_half_expansion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/12f88ee1-0486-4b14-9948-d09ab772f977
-- title:
--   SoficGroups.KunTransportedAmbientOverlap.transportedUnivFinpartition_half_expansion
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

theorem SoficGroups.KunTransportedAmbientOverlap.transportedUnivFinpartition_half_expansion
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (σ : ι → Equiv.Perm V) (T : Equiv.Perm V)
    (gamma : ℝ)
    (hexp : ∀ C ∈ Q.parts, ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        gamma * (E.card : ℝ) ≤
          (SoficGroups.boundary σ E : ℝ)) :
    ∀ C ∈ (SoficGroups.transportedUnivFinpartition Q T).parts,
      ∀ E : Finset V, E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i => T * σ i * T⁻¹) E : ℝ) := by sorry
