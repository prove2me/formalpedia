-- Prove2me | Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_exists_common_slow_overlap_scales_for_transported_partitions
-- name    : SoficGroups.KunTransportedAmbientOverlap.exists_common_slow_overlap_scales_for_transported_partitions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/8705a15c-a78d-40c8-8c5d-fe8ce77843fa
-- title:
--   SoficGroups.KunTransportedAmbientOverlap.exists_common_slow_overlap_scales_for_transported_partitions
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

theorem SoficGroups.KunTransportedAmbientOverlap.exists_common_slow_overlap_scales_for_transported_partitions
    {V : ℕ → Type*}
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Q : ∀ n, Finpartition (Finset.univ : Finset (V n)))
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (T : (n : ℕ) → κ → Equiv.Perm (V n))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hexp : ∀ n C, C ∈ (Q n).parts →
      ∀ E : Finset (V n), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (SoficGroups.boundary (σ n) E : ℝ))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary (σ n) C : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0))
    (htarget : ∀ j : κ, Tendsto
      (fun n =>
        (∑ D ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i => T n j * σ n i * (T n j)⁻¹) D : ℝ)) /
              Fintype.card (V n))
      atTop (nhds 0)) :
    ∃ eta H : ℕ → ℝ,
      (∀ n, 0 < eta n) ∧
        Antitone eta ∧
        Tendsto eta atTop (nhds 0) ∧
        (∀ n, 0 < H n) ∧
        Antitone H ∧
        Tendsto H atTop (nhds 0) ∧
        Tendsto (fun n => eta n / H n) atTop (nhds 0) ∧
        ∀ j : κ, Tendsto
          (fun n =>
            (∑ C ∈ SoficGroups.insufficientOverlapComponents
              (SoficGroups.transportedUnivFinpartition
                (Q n) (T n j))
              (Q n) (eta n), (C.card : ℝ)) /
                Fintype.card (V n))
          atTop (nhds 0) := by sorry
