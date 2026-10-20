-- Prove2me | Theorems.Thm_SoficGroups_SourceProductThroughAlpha_source_compressed_local_product_word_crossing_density_tendsto_zero
-- name    : SoficGroups.SourceProductThroughAlpha.source_compressed_local_product_word_crossing_density_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/0b9e4c9e-f734-4dd4-a1f2-171a1c8d64c4
-- title:
--   SoficGroups.SourceProductThroughAlpha.source_compressed_local_product_word_crossing_density_tendsto_zero
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
universe v

theorem SoficGroups.SourceProductThroughAlpha.source_compressed_local_product_word_crossing_density_tendsto_zero
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) =
          ⊤)
    (Q : ∀ n, Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                  i)) C : ℝ)) /
            (A.model n).size)
      atTop (𝓝 0))
    (z : SoficGroups.prefixElementaryGroup
          SoficGroups.alphaZeroPrefixCode ×
        SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
            SoficGroups.ThompsonPrefixLocal.sourceLocalWord) :
    Tendsto
      (fun n =>
        ((SoficGroups.partitionWordCrossing (Q n)
          ((A.model n).action
            (SoficGroups.ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding
              z))).card : ℝ) /
            (A.model n).size)
      atTop (𝓝 0) := by sorry
