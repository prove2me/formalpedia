-- Prove2me | Theorems.Thm_SoficGroups_KunActualCanonicalSelectedPruning_exists_actual_uniformly_expanding_pruned_selected_components
-- name    : SoficGroups.KunActualCanonicalSelectedPruning.exists_actual_uniformly_expanding_pruned_selected_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/b3e17fdb-b724-47eb-8dc3-aabb27f4b58c
-- title:
--   SoficGroups.KunActualCanonicalSelectedPruning.exists_actual_uniformly_expanding_pruned_selected_components
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualCanonicalSelectedPruning
open Filter Topology
open SoficGroups.MatchedComponentCompletion

theorem SoficGroups.KunActualCanonicalSelectedPruning.exists_actual_uniformly_expanding_pruned_selected_components
    {K J : Type*} [Group K] [Group J]
    (A : SoficGroups.SoficApproximation (K × J))
    (S : Finset K)
    (ν : ℕ → ℕ)
    (Q : (n : ℕ) → Finpartition
      (Finset.univ : Finset (Fin (A.model (ν n)).size)))
    (C : (n : ℕ) → Finset (Fin (A.model (ν n)).size))
    (hC : ∀ n, C n ∈ (Q n).parts)
    (hlarge : Tendsto (fun n => (C n).card) atTop atTop)
    (γ : ℝ) (hγ : 0 < γ)
    (a : ℕ → ℝ)
    (ha : Tendsto a atTop (nhds 0))
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
    ∃ (N : ℕ)
      (D : (n : ℕ) → Finset
        {x : Fin (A.model (ν (n + N))).size // x ∈ C (n + N)})
      (τ : (n : ℕ) → ↥S → Equiv.Perm
        {x : {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)} //
          x ∈ (Finset.univ \ D n :
            Finset {y : Fin (A.model (ν (n + N))).size //
              y ∈ C (n + N)})}),
      (∀ n,
        (Finset.univ \ D n :
          Finset {x : Fin (A.model (ν (n + N))).size //
            x ∈ C (n + N)}).Nonempty) ∧
      Tendsto
        (fun n => ((D n).card : ℝ) / (C (n + N)).card)
        atTop (nhds 0) ∧
      Tendsto
        (fun n =>
          (Finset.univ \ D n :
            Finset {x : Fin (A.model (ν (n + N))).size //
              x ∈ C (n + N)}).card)
        atTop atTop ∧
      (∀ n (i : ↥S)
        (x : {y : Fin (A.model (ν (n + N))).size //
          y ∈ C (n + N)})
        (hx : x ∈ (Finset.univ \ D n :
          Finset {y : Fin (A.model (ν (n + N))).size //
            y ∈ C (n + N)}))
        (_hi : completedRestriction
          ((A.model (ν (n + N))).action ((i : K), (1 : J)))
          (C (n + N)) x ∈
            (Finset.univ \ D n :
              Finset {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)})),
        ((τ n i ⟨x, hx⟩ :
          {z : {y : Fin (A.model (ν (n + N))).size //
                    y ∈ C (n + N)} //
            z ∈ (Finset.univ \ D n :
              Finset {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)})}) :
          {y : Fin (A.model (ν (n + N))).size //
            y ∈ C (n + N)}) =
            completedRestriction
              ((A.model (ν (n + N))).action ((i : K), (1 : J)))
              (C (n + N)) x) ∧
      (∀ n,
        ∀ E : Finset
          {x : {y : Fin (A.model (ν (n + N))).size //
                  y ∈ C (n + N)} //
            x ∈ (Finset.univ \ D n :
              Finset {y : Fin (A.model (ν (n + N))).size //
                y ∈ C (n + N)})},
          (γ / 2) * min (E.card : ℝ)
            ((Fintype.card
              {x : {y : Fin (A.model (ν (n + N))).size //
                      y ∈ C (n + N)} //
                x ∈ (Finset.univ \ D n :
                  Finset {y : Fin (A.model (ν (n + N))).size //
                    y ∈ C (n + N)})} : ℝ) - E.card) ≤
            (SoficGroups.boundary (τ n) E : ℝ)) := by sorry
