-- Prove2me | Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_dominant_component_loss_density_tendsto_zero
-- name    : SoficGroups.KunTransportedAmbientOverlap.dominant_component_loss_density_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/c4c033c9-f66e-4908-90a2-151b383c4156
-- title:
--   SoficGroups.KunTransportedAmbientOverlap.dominant_component_loss_density_tendsto_zero
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

theorem SoficGroups.KunTransportedAmbientOverlap.dominant_component_loss_density_tendsto_zero
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    {ι : Type*} [Fintype ι]
    (P Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hexp : ∀ n C, C ∈ (P n).parts →
      ∀ E : Finset (V n), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (SoficGroups.boundary (σ n) E : ℝ))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          (SoficGroups.boundary (σ n) C : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0))
    (htarget : Tendsto
      (fun n =>
        (∑ D ∈ (Q n).parts,
          (SoficGroups.boundary (σ n) D : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n))
      atTop (nhds 0) := by sorry
