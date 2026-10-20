-- Prove2me | Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_transported_partition_boundary_density_tendsto_zero
-- name    : SoficGroups.KunTransportedAmbientOverlap.transported_partition_boundary_density_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/784179ea-a2be-464a-b4e4-9672845afd9e
-- title:
--   SoficGroups.KunTransportedAmbientOverlap.transported_partition_boundary_density_tendsto_zero
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

theorem SoficGroups.KunTransportedAmbientOverlap.transported_partition_boundary_density_tendsto_zero
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {ι : Type*} [Fintype ι]
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (T : (n : ℕ) → Equiv.Perm (V n))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary (σ n) C : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈
          (SoficGroups.transportedUnivFinpartition (Q n) (T n)).parts,
            (SoficGroups.boundary
              (fun i => T n * σ n i * (T n)⁻¹) C : ℝ)) /
                Fintype.card (V n))
      atTop (nhds 0) := by sorry
