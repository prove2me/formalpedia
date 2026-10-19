-- Prove2me | Theorems.Thm_SoficGroups_KunCompletedProductDiagonalSparseCut_exists_completed_goodPermutationGraph_sparse_cut
-- name    : SoficGroups.KunCompletedProductDiagonalSparseCut.exists_completed_goodPermutationGraph_sparse_cut
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/05a6a1a3-bea1-4b71-a533-d988f383ebe2
-- title:
--   SoficGroups.KunCompletedProductDiagonalSparseCut.exists_completed_goodPermutationGraph_sparse_cut
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedProductDiagonalSparseCut
open SoficGroups.KunDiagonalGoodRootGraphLoss
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
universe u

theorem SoficGroups.KunCompletedProductDiagonalSparseCut.exists_completed_goodPermutationGraph_sparse_cut
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (γ α : ℝ) (hγ : 0 < γ) (hα : 0 < α)
    (hγsmall :
      216 * γ <
        (S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2) :
    ∃ r : ℕ,
      ∀ (V : Type u) [Fintype V] [DecidableEq V]
        (σ : ↥S → Equiv.Perm V) (φ : G → Equiv.Perm V),
      (∀ g : G, φ g = ((w g).map σ).prod) →
      φ 1 = 1 →
      (∀ i : ↥S, φ (i : G) = σ i) →
      ∀ (p : Equiv.Perm V) (B : Finset V),
      (∀ a g : G,
        (w a).length + (w g).length + (w (a * g)).length ≤ r →
          ∀ x : V, x ∉ B →
            φ (a * g) x = (φ a * φ g) x) →
      let T := goodPermutationGraph p B
      T.Nonempty →
      (SoficGroups.boundary
        (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) <
          γ * (T.card : ℝ) →
      ∃ U : Finset (V × V),
        (((U ∆ T).card : ℝ)) ≤
          72 * (SoficGroups.boundary
            (fun i : ↥S => (σ i).prodCongr (σ i)) T : ℝ) /
              ((S.card : ℝ) *
                (1 - kazhdanMarkovContractionFactor P S) ^ 2) ∧
        3 * (U ∆ T).card < T.card ∧
        (SoficGroups.boundary
          (fun i : ↥S => (σ i).prodCongr (σ i)) U : ℝ) ≤
            α * (U.card : ℝ) := by sorry
