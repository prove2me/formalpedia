-- Prove2me | Theorems.Thm_SoficGroups_SourceProductThroughAlpha_source_u_transported_reference_half_expansion
-- name    : SoficGroups.SourceProductThroughAlpha.source_u_transported_reference_half_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/d0973f01-e00d-4fa8-98b4-cc20145830a5
-- title:
--   SoficGroups.SourceProductThroughAlpha.source_u_transported_reference_half_expansion
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceProductThroughAlpha
open Filter Topology
open scoped BigOperators

theorem SoficGroups.SourceProductThroughAlpha.source_u_transported_reference_half_expansion
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (QΓ : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (gamma : ℝ)
    (hexpand : ∀ n, ∀ C ∈ (QΓ n).parts,
      ∀ E : Finset (Fin (A.model n).size), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                    i)) E : ℝ)) :
    ∀ n, ∀ C ∈
      (SoficGroups.transportedUnivFinpartition
        (QΓ n)
        ((A.model n).action
          SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)).parts,
      ∀ E : Finset (Fin (A.model n).size), E ⊆ C →
        2 * E.card ≤ C.card →
          gamma * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                    SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement *
                  (A.model n).action
                    (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                      i) *
                    ((A.model n).action
                      SoficGroups.SourceBothCompressionNormalization.sourceCompressionUElement)⁻¹)
              E : ℝ) := by sorry
