-- Prove2me | Theorems.Thm_SoficGroups_KunLiteralNineSourceCompletedCentralizerModels_exists_source_common_log_rank_with_ambient_midrank_variance
-- name    : SoficGroups.KunLiteralNineSourceCompletedCentralizerModels.exists_source_common_log_rank_with_ambient_midrank_variance
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/9644469c-6055-4f06-bb5c-ea20a32e195d
-- title:
--   SoficGroups.KunLiteralNineSourceCompletedCentralizerModels.exists_source_common_log_rank_with_ambient_midrank_variance
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunLiteralNineSourceCompletedCentralizerModels
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunLiteralNineSourceCompletedCentralizerModels.exists_source_common_log_rank_with_ambient_midrank_variance
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (SG : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (QΓ QG : (n : ℕ) →
      Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
    (γG : ℝ)
    (hsymmetricG : ∀ g ∈ SG, g⁻¹ ∈ SG)
    (hgeneratesG : Subgroup.closure
      (SG : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode)) =
          ⊤)
    (hpositive : Subgroup.closure
      (Set.range
        (SoficGroups.KunExactActualSourceAmbientGenerators.sourcePositiveGeneratorMap
          SΓ)) = ⊤)
    (hγG : 0 < γG)
    (hexpandG : ∀ n C, C ∈ (QG n).parts →
      ∀ E : Finset (Fin (A.model n).size), E ⊆ C →
        2 * E.card ≤ C.card →
          γG * (E.card : ℝ) ≤
            (SoficGroups.boundary
              (fun i : ↥SG =>
                (A.model n).action
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.ninePrefixCode)) E : ℝ))
    (hboundaryΓ : Tendsto
      (fun n =>
        (∑ C ∈ (QΓ n).parts,
          (SoficGroups.boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                (SoficGroups.KunExactActualSourceAmbientGenerators.sourceAlphaInclusion
                  (i : SoficGroups.prefixElementaryGroup
                    SoficGroups.alphaPrefixCode))) C : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0))
    (hboundaryG : Tendsto
      (fun n =>
        (∑ C ∈ (QG n).parts,
          (SoficGroups.boundary
            (fun i : ↥SG =>
              (A.model n).action
                (i : SoficGroups.prefixElementaryGroup
                  SoficGroups.ninePrefixCode)) C : ℝ)) /
              (A.model n).size)
      atTop (𝓝 0))
    (eta H : ℕ → ℝ)
    (heta0 : ∀ n, 0 ≤ eta n)
    (heta1 : ∀ n, eta n < 1)
    (hH : ∀ n, 0 < H n)
    (heta : Tendsto eta atTop (𝓝 0))
    (hratio : Tendsto (fun n => eta n / H n) atTop (𝓝 0))
    (hoverlap : ∀ j : Fin 2, Tendsto
      (fun n =>
        (∑ C ∈ SoficGroups.insufficientOverlapComponents
          (SoficGroups.transportedUnivFinpartition
            (QΓ n)
            ((A.model n).action
              (SoficGroups.KunExactActualSourceAmbientGenerators.sourceCompressionTable
                j)))
          (QΓ n) (eta n), (C.card : ℝ)) /
            (A.model n).size)
      atTop (𝓝 0))
    (hloss : ∀ j : Fin 2, Tendsto
      (fun n =>
        (∑ C ∈
          (SoficGroups.transportedUnivFinpartition
            (QΓ n)
            ((A.model n).action
              (SoficGroups.KunExactActualSourceAmbientGenerators.sourceCompressionTable
                j))).parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart (QΓ n) C).card : ℝ))) /
              (A.model n).size)
      atTop (𝓝 0)) :
    ∃ r : ℕ → ℝ,
      (∀ n, r n ∈ Set.Ico 0 (H n)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (QG n).parts,
            (C.card : ℝ) *
              SoficGroups.midrankVariance
                (SoficGroups.componentRankMassList C
                  (SoficGroups.SourceCommonOffsetMidrankEnergy.componentLogRank
                    (QΓ n) (H n) (r n)))) /
                (A.model n).size)
        atTop (𝓝 0) ∧
      (∀ j : Fin 2, Tendsto
        (fun n =>
          ((SoficGroups.partitionWordCrossing (QG n)
            (((A.model n).action
              (SoficGroups.KunExactActualSourceAmbientGenerators.sourceCompressionTable
                j))⁻¹)).card : ℝ) /
              (A.model n).size)
        atTop (𝓝 0)) := by sorry
