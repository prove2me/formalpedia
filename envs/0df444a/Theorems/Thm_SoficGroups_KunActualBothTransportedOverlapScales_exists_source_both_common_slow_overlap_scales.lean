-- Prove2me | Theorems.Thm_SoficGroups_KunActualBothTransportedOverlapScales_exists_source_both_common_slow_overlap_scales
-- name    : SoficGroups.KunActualBothTransportedOverlapScales.exists_source_both_common_slow_overlap_scales
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/2bd32f51-af13-4c83-80a5-0044e995bc0b
-- title:
--   SoficGroups.KunActualBothTransportedOverlapScales.exists_source_both_common_slow_overlap_scales
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualBothTransportedOverlapScales
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunActualBothTransportedOverlapScales.exists_source_both_common_slow_overlap_scales
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hexpand : ∀ n C, C ∈ (Q n).parts →
      ∀ E : Finset (Fin (A.model n).size), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥S =>
                (A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                    (i : SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode))) E : ℝ))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥S =>
              (A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.alphaPrefixCode))) C : ℝ)) /
              (A.model n).size)
      atTop (nhds 0)) :
    ∃ eta H : ℕ → ℝ,
      (∀ n, 0 < eta n) ∧
      Antitone eta ∧
      Tendsto eta atTop (nhds 0) ∧
      (∀ n, 0 < H n) ∧
      Antitone H ∧
      Tendsto H atTop (nhds 0) ∧
      Tendsto (fun n => eta n / H n) atTop (nhds 0) ∧
      (∀ j : Fin 2, Tendsto
        (fun n =>
          (∑ C ∈ SoficGroups.insufficientOverlapComponents
            (SoficGroups.transportedUnivFinpartition
              (Q n)
              ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j)))
            (Q n) (eta n), (C.card : ℝ)) /
              (A.model n).size)
        atTop (nhds 0)) ∧
      (∀ j : Fin 2, Tendsto
        (fun n =>
          (∑ C ∈
            (SoficGroups.transportedUnivFinpartition
              (Q n)
              ((A.model n).action
                (SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable j))).parts,
            ((C.card : ℝ) -
              ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
                (A.model n).size)
        atTop (nhds 0)) ∧
      ∃ N : ℕ, ∀ n : ℕ, eta (n + N) < 1 := by sorry
