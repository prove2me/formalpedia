-- Prove2me | Theorems.Thm_SoficGroups_KunUnconditionalActualSourceDecomposition_exists_unconditional_actual_source_dual_finpartition_sequences
-- name    : SoficGroups.KunUnconditionalActualSourceDecomposition.exists_unconditional_actual_source_dual_finpartition_sequences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/9761247b-e430-40a9-a0c1-529e3ed64756
-- title:
--   SoficGroups.KunUnconditionalActualSourceDecomposition.exists_unconditional_actual_source_dual_finpartition_sequences
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUnconditionalActualSourceDecomposition
open Filter Topology
open SoficGroups.KunSourceUnconditionalFullDecomposition
open SoficGroups.KunExactActualSourceAmbientGenerators
open SoficGroups.KunUnconditionalActualSourceGeneratorData

theorem SoficGroups.KunUnconditionalActualSourceDecomposition.exists_unconditional_actual_source_dual_finpartition_sequences
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup
        SoficGroups.ninePrefixCode)) :
    ∃ (SΓ : Finset
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode))
      (SG : Finset
          (SoficGroups.prefixElementaryGroup
            SoficGroups.ninePrefixCode))
      (QΓ QG : (n : ℕ) →
        Finpartition
          (Finset.univ : Finset (Fin (A.model n).size)))
      (γΓ γG : ℝ),
      SG = sourceAmbientSymmetricGenerators SΓ ∧
      1 ∈ SΓ ∧
      (∀ g ∈ SΓ, g⁻¹ ∈ SΓ) ∧
      Subgroup.closure
        (SΓ : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode)) = ⊤ ∧
      1 ∈ SG ∧
      (∀ g ∈ SG, g⁻¹ ∈ SG) ∧
      Subgroup.closure
        (SG : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.ninePrefixCode)) = ⊤ ∧
      Function.Injective sourceAlphaInclusion ∧
      Subgroup.closure
        (Set.range (sourcePositiveGeneratorMap SΓ)) = ⊤ ∧
      0 < γΓ ∧
      0 < γG ∧
      (∀ n, ∀ C ∈ (QΓ n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γΓ * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (sourceAlphaInclusion (i :
                    SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode))) E : ℝ)) ∧
      (∀ n, ∀ C ∈ (QG n).parts,
        ∀ E : Finset (Fin (A.model n).size),
          E ⊆ C →
          2 * E.card ≤ C.card →
          γG * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SG =>
                (A.model n).action (i :
                  SoficGroups.prefixElementaryGroup
                    SoficGroups.ninePrefixCode)) E : ℝ)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QΓ n).parts,
            (SoficGroups.boundary
              (fun i : ↥SΓ =>
                (A.model n).action
                  (sourceAlphaInclusion (i :
                    SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaPrefixCode))) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QG n).parts,
            (SoficGroups.boundary
              (fun i : ↥SG =>
                (A.model n).action (i :
                  SoficGroups.prefixElementaryGroup
                    SoficGroups.ninePrefixCode)) C : ℝ)) /
                (A.model n).size)
        atTop (𝓝 0) := by sorry
