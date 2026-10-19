-- Prove2me | Theorems.Thm_SoficGroups_KunSourceUnconditionalFullDecomposition_exists_source_sparse_cut_at_radius
-- name    : SoficGroups.KunSourceUnconditionalFullDecomposition.exists_source_sparse_cut_at_radius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/8c65e042-e976-40dc-bc3a-c2bc0e0d16cd
-- title:
--   SoficGroups.KunSourceUnconditionalFullDecomposition.exists_source_sparse_cut_at_radius
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunSourceUnconditionalFullDecomposition
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.KunActualRootedModelBridge
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff

theorem SoficGroups.KunSourceUnconditionalFullDecomposition.exists_source_sparse_cut_at_radius
    {G : Type} [Group G] [DecidableEq G]
    (P : SoficGroups.KazhdanPair.{0, 0} G)
    (S : Finset G) (hone : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (γ α : ℝ) (hγ : 0 < γ) (hα : 0 < α)
    (hsmall :
      216 * γ <
        (S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2) :
    ∃ r : ℕ,
      ∀ (A : SoficGroups.SoficApproximation G) (n : ℕ)
        (T : Finset (Fin (A.model n).size)),
      Disjoint T
        (chosenCayleyRadiusBad A S
          (symmetricGeneratorWord S hsymmetric hgenerates) n r) →
      (SoficGroups.boundary
        (fun i : ↥S => (A.model n).action (i : G)) T : ℝ) <
          γ * (T.card : ℝ) →
      ∃ U : Finset (Fin (A.model n).size),
        3 * (U ∆ T).card < T.card ∧
          (SoficGroups.boundary
            (fun i : ↥S => (A.model n).action (i : G)) U : ℝ) ≤
              α * (U.card : ℝ) := by sorry
