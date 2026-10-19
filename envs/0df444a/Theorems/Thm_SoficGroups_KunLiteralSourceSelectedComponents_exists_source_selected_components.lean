-- Prove2me | Theorems.Thm_SoficGroups_KunLiteralSourceSelectedComponents_exists_source_selected_components
-- name    : SoficGroups.KunLiteralSourceSelectedComponents.exists_source_selected_components
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/cdbb6b87-8b0b-44cb-b631-ff570d76ba85
-- title:
--   SoficGroups.KunLiteralSourceSelectedComponents.exists_source_selected_components
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunLiteralSourceSelectedComponents
open Filter Topology
open scoped BigOperators Pointwise

theorem SoficGroups.KunLiteralSourceSelectedComponents.exists_source_selected_components
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (F : Finset
      (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
        SoficGroups.ThompsonPrefixLocal.sourceLocalWord)) :
    ∃ (S : Finset
          (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
      (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
      (hgenerates : Subgroup.closure
        (S : Set
          (SoficGroups.prefixElementaryGroup
            SoficGroups.alphaPrefixCode)) = ⊤)
      (Q : (n : ℕ) →
        Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
      (gamma : ℝ) (N : ℕ) (r : ℕ → ℕ)
      (C : (n : ℕ) → Finset (Fin (A.model (n + N)).size)),
      1 ∈ S ∧
      0 < gamma ∧
      Tendsto
        (fun n =>
          (∑ D ∈ (Q n).parts,
            (SoficGroups.boundary
              (fun i : ↥S =>
                (A.model n).action
                  (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                    i)) D : ℝ)) /
              (A.model n).size)
        atTop (𝓝 0) ∧
      Tendsto r atTop atTop ∧
      (∀ n, C n ∈ (sourceTransportedPartition A Q (n + N)).parts) ∧
      (∀ n, (C n).Nonempty) ∧
      (∀ n, ∀ D : Finset (Fin (A.model (n + N)).size),
        D ⊆ C n → 2 * D.card ≤ (C n).card →
          gamma * (D.card : ℝ) ≤
            (SoficGroups.boundary
              (sourceTransportedReferenceGenerators A S (n + N)) D : ℝ)) ∧
      Tendsto
        (fun n =>
          (SoficGroups.boundary
            (sourceTransportedReferenceGenerators A S (n + N))
            (C n) : ℝ) / (C n).card)
        atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          (((C n ∩ SoficGroups.matchedRadiusBad
            (sourceTransportedPartition A Q (n + N))
            (sourceSelectedProductRadiusLabels S F (r n))
            (((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
              A).model (n + N)).action)
            (sourceSelectedRadiusBad A S
              hsymmetric hgenerates F (n + N) (r n))).card : ℝ) /
                (C n).card))
        atTop (𝓝 0) ∧
      Tendsto (fun n => (C n).card) atTop atTop := by sorry
