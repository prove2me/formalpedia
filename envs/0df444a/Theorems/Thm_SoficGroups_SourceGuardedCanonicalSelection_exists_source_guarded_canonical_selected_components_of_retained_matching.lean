-- Prove2me | Theorems.Thm_SoficGroups_SourceGuardedCanonicalSelection_exists_source_guarded_canonical_selected_components_of_retained_matching
-- name    : SoficGroups.SourceGuardedCanonicalSelection.exists_source_guarded_canonical_selected_components_of_retained_matching
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/752fd2f0-50bd-41be-8414-4e82b80371aa
-- title:
--   SoficGroups.SourceGuardedCanonicalSelection.exists_source_guarded_canonical_selected_components_of_retained_matching
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGuardedCanonicalSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff

theorem SoficGroups.SourceGuardedCanonicalSelection.exists_source_guarded_canonical_selected_components_of_retained_matching
    [DecidableEq SourceK] [DecidableEq SourceJ]
    (A : SoficGroups.SoficApproximation
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode))
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hone : 1 ∈ SΓ)
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) =
          ⊤)
    (P Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model n).size)))
    {κ : Type*} [Fintype κ]
    (σ : (n : ℕ) → κ → Equiv.Perm (Fin (A.model n).size))
    (R : (n : ℕ) → Finset (Finset (Fin (A.model n).size)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : (n : ℕ) → Finset (Fin (A.model n).size) →
      Finset (Fin (A.model n).size))
    (hD : ∀ n C, C ∈ R n → D n C ∈ (Q n).parts)
    (H eta : ℕ → ℝ)
    (hH : Tendsto H atTop (nhds 0))
    (heta : Tendsto eta atTop (nhds 0))
    (hmajor : ∀ n,
      eta n ≤ (1 : ℝ) / 2 →
      2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
        ∀ C, C ∈ R n →
          (D n C).card < 2 * (C ∩ D n C).card)
    (hdiscard : Tendsto
      (fun n =>
        ((((Finset.univ : Finset (Fin (A.model n).size)) \
          SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
            (A.model n).size))
      atTop (nhds 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) /
          (A.model n).size)
      atTop (nhds 0))
    (F : Finset SourceJ)
    (E : (n : ℕ) → ℕ → Finset (Fin (A.model n).size))
    (hE : ∀ k, Tendsto
      (fun n => ((E n k).card : ℝ) / (A.model n).size)
      atTop (nhds 0))
    (hsource : Tendsto
      (fun n =>
        (∑ C ∈ (Q n).parts,
          (SoficGroups.boundary
            (fun i : ↥SΓ =>
              (A.model n).action
                (SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion
                  i)) C : ℝ)) /
            (A.model n).size)
      atTop (nhds 0))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (SoficGroups.boundary (σ n) C : ℝ)) /
          (A.model n).size)
      atTop (nhds 0))
    (N₀ : ℕ) :
    ∃ (N : ℕ) (r : ℕ → ℕ)
      (C : (n : ℕ) → Finset (Fin (A.model (n + N)).size)),
      N₀ ≤ N ∧
      (∀ n, eta (n + N) ≤ (1 : ℝ) / 2) ∧
      (∀ n,
        2 * (Real.exp (H (n + N)) - 1 +
          2 * eta (n + N)) < 1) ∧
      Tendsto r atTop atTop ∧
      (∀ n, C n ∈ R (n + N)) ∧
      Tendsto
        (fun n =>
          (SoficGroups.boundary (σ (n + N)) (C n) : ℝ) /
            (C n).card)
        atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          (((C n ∩ SoficGroups.matchedRadiusBad
            (P (n + N))
            (SoficGroups.CanonicalProductRadiusBadMatchedCapture.sourceProductRadiusLabels
              (SoficGroups.SourceProductThroughAlpha.sourceCompressedGeneratingFinset SΓ)
              F (r n))
            (((SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductApproximation
              A).model (n + N)).action)
            (guardedCanonicalProductRadiusBad
              A SΓ hsymmetric hgenerates F E (n + N) (r n))).card : ℝ) /
                (C n).card))
        atTop (nhds 0) ∧
      Tendsto (fun n => (C n).card) atTop atTop := by sorry
