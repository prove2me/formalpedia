-- Prove2me | Theorems.Thm_SoficGroups_KunActualSourceSelectedCompletedGeneratorExpansion_exists_vanishing_completed_first_factor_additive_expansion_of_selected_source
-- name    : SoficGroups.KunActualSourceSelectedCompletedGeneratorExpansion.exists_vanishing_completed_first_factor_additive_expansion_of_selected_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/4e65e2ae-f73b-4ab6-aa25-8dc0b4636a6c
-- title:
--   SoficGroups.KunActualSourceSelectedCompletedGeneratorExpansion.exists_vanishing_completed_first_factor_additive_expansion_of_selected_source
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSourceSelectedCompletedGeneratorExpansion
open Filter Topology
open scoped BigOperators

theorem SoficGroups.KunActualSourceSelectedCompletedGeneratorExpansion.exists_vanishing_completed_first_factor_additive_expansion_of_selected_source
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (S : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure
      (S : Set
        (SoficGroups.prefixElementaryGroup
          SoficGroups.alphaPrefixCode)) = ⊤)
    (Q : (n : ℕ) →
      Finpartition (Finset.univ : Finset (Fin (A.model n).size)))
    (F : Finset
      (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
        SoficGroups.ThompsonPrefixLocal.sourceLocalWord))
    (N : ℕ) (r : ℕ → ℕ)
    (C : (n : ℕ) → Finset (Fin (A.model (n + N)).size))
    (gamma : ℝ)
    (hC : ∀ n, (C n).Nonempty)
    (hexpand : ∀ n, ∀ D : Finset (Fin (A.model (n + N)).size),
      D ⊆ C n → 2 * D.card ≤ (C n).card →
        gamma * (D.card : ℝ) ≤
          (SoficGroups.boundary
            (SoficGroups.KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerators
              A S (n + N)) D : ℝ))
    (hboundary : Tendsto
      (fun n =>
        (SoficGroups.boundary
          (SoficGroups.KunLiteralSourceSelectedComponents.sourceTransportedReferenceGenerators
            A S (n + N)) (C n) : ℝ) / (C n).card)
      atTop (nhds 0))
    (hguarded : Tendsto
      (fun n =>
        (((C n ∩ SoficGroups.matchedRadiusBad
          (SoficGroups.KunLiteralSourceSelectedComponents.sourceTransportedPartition
            A Q (n + N))
          (SoficGroups.KunLiteralSourceSelectedComponents.sourceSelectedProductRadiusLabels
            S F (r n))
          (((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
            A).model (n + N)).action)
          (SoficGroups.KunLiteralSourceSelectedComponents.sourceSelectedRadiusBad
            A S hsymmetric hgenerates F (n + N) (r n))).card : ℝ) /
              (C n).card))
      atTop (nhds 0)) :
    ∃ a : ℕ → ℝ,
      (∀ n, 0 ≤ a n) ∧
      Tendsto a atTop (nhds 0) ∧
      ∀ n, ∀ E : Finset
        {x : Fin (A.model (n + N)).size // x ∈ C n},
        gamma * min (E.card : ℝ)
          ((Fintype.card
            {x : Fin (A.model (n + N)).size // x ∈ C n} : ℝ) -
              E.card) -
          a n * Fintype.card
            {x : Fin (A.model (n + N)).size // x ∈ C n} ≤
            (SoficGroups.boundary
              (fun i :
                ↥(SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset
                  S) =>
                SoficGroups.MatchedComponentCompletion.completedRestriction
                  (((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
                    A).model (n + N)).action
                    ((i : SoficGroups.prefixElementaryGroup
                      SoficGroups.alphaZeroPrefixCode), 1))
                  (C n)) E : ℝ) := by sorry
