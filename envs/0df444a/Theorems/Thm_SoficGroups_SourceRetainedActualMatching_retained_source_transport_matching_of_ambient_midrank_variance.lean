-- Prove2me | Theorems.Thm_SoficGroups_SourceRetainedActualMatching_retained_source_transport_matching_of_ambient_midrank_variance
-- name    : SoficGroups.SourceRetainedActualMatching.retained_source_transport_matching_of_ambient_midrank_variance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/436280a0-7a2d-40bd-99e6-e7166aa6c6d2
-- title:
--   SoficGroups.SourceRetainedActualMatching.retained_source_transport_matching_of_ambient_midrank_variance
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

theorem SoficGroups.SourceRetainedActualMatching.retained_source_transport_matching_of_ambient_midrank_variance
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (κ : Type*)
    (Q A : (n : ℕ) → Finpartition
      (Finset.univ : Finset (V n)))
    (T : (n : ℕ) → κ → Equiv.Perm (V n))
    (H r eta : ℕ → ℝ)
    (hHpos : ∀ n, 0 < H n)
    (hHzero : Tendsto H atTop (nhds 0))
    (heta0 : ∀ n, 0 ≤ eta n)
    (hetazero : Tendsto eta atTop (nhds 0))
    (hvariance : Tendsto
      (fun n =>
        (∑ C ∈ (A n).parts,
          (C.card : ℝ) *
            SoficGroups.midrankVariance
              (SoficGroups.componentRankMassList C
                (logarithmicComponentRank (Q n) (H n) (r n)))) /
                  Fintype.card (V n))
      atTop (nhds 0))
    (hcross : ∀ i : κ, Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing
          (A n) (T n i).symm).card : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0))
    (hoverlap : ∀ i : κ, Tendsto
      (fun n =>
        ((∑ C ∈ SoficGroups.insufficientOverlapComponents
          (SoficGroups.transportedUnivFinpartition (Q n) (T n i))
          (Q n) (eta n), C.card : ℕ) : ℝ) /
            Fintype.card (V n))
      atTop (nhds 0)) :
    ∀ i : κ,
      (∀ n, retainedTransportedComponents
        (Q n) (T n i) (H n) (r n) (eta n) ⊆
          (SoficGroups.transportedUnivFinpartition
            (Q n) (T n i)).parts) ∧
      (∀ n C, C ∈ retainedTransportedComponents
        (Q n) (T n i) (H n) (r n) (eta n) →
          SoficGroups.maximumOverlapPart (Q n) C ∈ (Q n).parts) ∧
      (∀ n, eta n ≤ (1 : ℝ) / 2 →
        2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
          ∀ C, C ∈ retainedTransportedComponents
            (Q n) (T n i) (H n) (r n) (eta n) →
              (SoficGroups.maximumOverlapPart (Q n) C).card <
                2 * (C ∩ SoficGroups.maximumOverlapPart
                  (Q n) C).card) ∧
      Tendsto
        (fun n =>
          (((Finset.univ : Finset (V n)) \
            SoficGroups.matchedRetainedSupport
              (retainedTransportedComponents
                (Q n) (T n i) (H n) (r n) (eta n))).card : ℝ) /
              Fintype.card (V n))
        atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          ((∑ C ∈ retainedTransportedComponents
            (Q n) (T n i) (H n) (r n) (eta n),
              (C ∆ SoficGroups.maximumOverlapPart (Q n) C).card :
                ℕ) : ℝ) / Fintype.card (V n))
        atTop (nhds 0) ∧
      (∀ n, 2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
        Set.InjOn (SoficGroups.maximumOverlapPart (Q n))
          ((retainedTransportedComponents
            (Q n) (T n i) (H n) (r n) (eta n) :
              Finset (Finset (V n))) :
                Set (Finset (V n)))) := by sorry
