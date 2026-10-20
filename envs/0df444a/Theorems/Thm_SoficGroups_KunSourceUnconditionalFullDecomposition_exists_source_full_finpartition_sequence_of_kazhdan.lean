-- Prove2me | Theorems.Thm_SoficGroups_KunSourceUnconditionalFullDecomposition_exists_source_full_finpartition_sequence_of_kazhdan
-- name    : SoficGroups.KunSourceUnconditionalFullDecomposition.exists_source_full_finpartition_sequence_of_kazhdan
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/ae1667bb-0932-47eb-8ed7-e5dddddfaa2a
-- title:
--   SoficGroups.KunSourceUnconditionalFullDecomposition.exists_source_full_finpartition_sequence_of_kazhdan
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

theorem SoficGroups.KunSourceUnconditionalFullDecomposition.exists_source_full_finpartition_sequence_of_kazhdan
    {G : Type} [Group G] [DecidableEq G]
    (A : SoficGroups.SoficApproximation G)
    (P : SoficGroups.KazhdanPair.{0, 0} G)
    (S : Finset G) (hone : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) :
    ∃ (γ : ℝ)
      (Q : (n : ℕ) →
        Finpartition
          (Finset.univ : Finset (Fin (A.model n).size))),
      0 < γ ∧
        (∀ n, ∀ C ∈ (Q n).parts,
          ∀ E : Finset (Fin (A.model n).size),
            E ⊆ C →
            2 * E.card ≤ C.card →
            γ * (E.card : ℝ) ≤
              (SoficGroups.boundary
                (fun i : ↥S =>
                  (A.model n).action (i : G)) E : ℝ)) ∧
        Tendsto
          (fun n =>
            (∑ C ∈ (Q n).parts,
              (SoficGroups.boundary
                (fun i : ↥S =>
                  (A.model n).action (i : G)) C : ℝ)) /
                  (A.model n).size)
          atTop (𝓝 0) := by sorry
