-- Prove2me | Theorems.Thm_SoficGroups_KunActualCanonicalSelectedFiniteModelComposition_nonempty_expandingCentralizerFiniteModel_of_canonical_selected_additive
-- name    : SoficGroups.KunActualCanonicalSelectedFiniteModelComposition.nonempty_expandingCentralizerFiniteModel_of_canonical_selected_additive
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/a5d49e04-7116-4c3c-9e05-de37692f91b7
-- title:
--   SoficGroups.KunActualCanonicalSelectedFiniteModelComposition.nonempty_expandingCentralizerFiniteModel_of_canonical_selected_additive
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualCanonicalSelectedFiniteModelComposition
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CanonicalProductRadiusBadMatchedCapture

theorem SoficGroups.KunActualCanonicalSelectedFiniteModelComposition.nonempty_expandingCentralizerFiniteModel_of_canonical_selected_additive
    {K J : Type} [Group K] [Group J]
    [DecidableEq K] [DecidableEq J]
    (A : SoficGroups.SoficApproximation (K × J))
    (P : SoficGroups.KazhdanPair.{0, 0} K)
    (S : Finset K) (hone : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set K) = ⊤)
    (F : Finset J) (ν : ℕ → ℕ)
    (Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model (ν n)).size)))
    (C : (n : ℕ) → Finset (Fin (A.model (ν n)).size))
    (hC : ∀ n, C n ∈ (Q n).parts)
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (hmatched : Tendsto
      (fun n =>
        (((C n ∩ SoficGroups.matchedRadiusBad
          (Q n) (sourceProductRadiusLabels S F (r n))
          ((A.model (ν n)).action)
          (canonicalProductRadiusBad
            A S hsymmetric hgenerates F (ν n) (r n))).card : ℝ) /
            (C n).card))
      atTop (𝓝 0))
    (hlarge : Tendsto (fun n => (C n).card) atTop atTop)
    (γ : ℝ) (hγ : 0 < γ)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (hadd : ∀ n,
      ∀ E : Finset {x : Fin (A.model (ν n)).size // x ∈ C n},
        γ * min (E.card : ℝ)
            ((Fintype.card
              {x : Fin (A.model (ν n)).size // x ∈ C n} : ℝ) -
              E.card) -
          a n * Fintype.card
            {x : Fin (A.model (ν n)).size // x ∈ C n} ≤
          (SoficGroups.boundary
            (fun i : ↥S =>
              completedRestriction
                ((A.model (ν n)).action ((i : K), (1 : J)))
                (C n)) E : ℝ)) :
    Nonempty (SoficGroups.ExpandingCentralizerFiniteModel J F) := by sorry
