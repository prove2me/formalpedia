-- Prove2me | Theorems.Thm_SoficGroups_KunActualSourceURetainedNoPremise_exists_actual_source_u_retained_matching
-- name    : SoficGroups.KunActualSourceURetainedNoPremise.exists_actual_source_u_retained_matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/d6a04943-dff8-48da-afbd-acbdcc10a02f
-- title:
--   SoficGroups.KunActualSourceURetainedNoPremise.exists_actual_source_u_retained_matching
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSourceURetainedNoPremise
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.KunActualSourceURetainedNoPremise.exists_actual_source_u_retained_matching
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode)) :
    ∃ (SΓ : Finset
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode))
      (QΓ : (n : ℕ) →
        Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
      (γΓ : ℝ)
      (H eta r : ℕ → ℝ)
      (R : (n : ℕ) → Finset (Finset (Fin (A.model n).size))),
      1 ∈ SΓ ∧
      (∀ g ∈ SΓ, g⁻¹ ∈ SΓ) ∧
      Subgroup.closure
        (SΓ : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode)) = ⊤ ∧
      0 < γΓ ∧
      (∀ n, ∀ C ∈ (QΓ n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γΓ * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                    (i : SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode))) E : ℝ)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QΓ n).parts,
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (SoficGroups.SourceBothCompressionNormalization.sourceAlphaElement
                    (i : SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode))) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      (∀ n, 0 < H n) ∧
      Tendsto H atTop (𝓝 0) ∧
      (∀ n, 0 < eta n) ∧
      (∀ n, eta n < 1) ∧
      Tendsto eta atTop (𝓝 0) ∧
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
      (∀ n,
        R n =
          SoficGroups.SourceRetainedActualMatching.retainedTransportedComponents
            (QΓ n)
            ((A.model n).action
              SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)
            (H n) (r n) (eta n)) ∧
      (∀ n,
        R n ⊆
          (SoficGroups.transportedUnivFinpartition
            (QΓ n)
            ((A.model n).action
              SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)).parts) ∧
      (∀ n C, C ∈ R n →
        SoficGroups.maximumOverlapPart (QΓ n) C ∈ (QΓ n).parts) ∧
      (∀ n, eta n ≤ (1 : ℝ) / 2 →
        2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
          ∀ C, C ∈ R n →
            (SoficGroups.maximumOverlapPart (QΓ n) C).card <
              2 * (C ∩ SoficGroups.maximumOverlapPart
                (QΓ n) C).card) ∧
      Tendsto
        (fun n =>
          (((Finset.univ : Finset (Fin (A.model n).size)) \
            SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
              (A.model n).size)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          ((∑ C ∈ R n,
            (C ∆ SoficGroups.maximumOverlapPart
              (QΓ n) C).card : ℕ) : ℝ) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      (∀ n, 2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
        Set.InjOn (SoficGroups.maximumOverlapPart (QΓ n))
          ((R n : Finset (Finset (Fin (A.model n).size))) :
            Set (Finset (Fin (A.model n).size)))) := by sorry
