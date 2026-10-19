-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_exists_rooted_word_radius_sparse_cut_of_boundary
-- name    : SoficGroups.KunRootedWordPower.exists_rooted_word_radius_sparse_cut_of_boundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/b0c767d1-e713-4d40-a158-65abce1d9def
-- title:
--   SoficGroups.KunRootedWordPower.exists_rooted_word_radius_sparse_cut_of_boundary
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise symmDiff
universe u
attribute [local instance] SoficGroups.KunRootedWordPower.rootedSparseModelDecidableEq

theorem SoficGroups.KunRootedWordPower.exists_rooted_word_radius_sparse_cut_of_boundary
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (γ α : ℝ) (_hγ : 0 < γ) (hα : 0 < α)
    (hγsmall :
      216 * γ <
        (S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2) :
    ∃ (k r : ℕ), ∀ X : RootedIndicatorMarkovModel G ↥S,
      X.IsGenerated (fun i : ↥S => (i : G)) w →
      X.IsRootedAtRadius w r →
      ∀ T : Finset X.carrier,
        T.Nonempty →
        (∀ x : X.carrier,
          X.indicator x = if x ∈ T then (1 : ℝ) else 0) →
        (SoficGroups.boundary X.generator T : ℝ) <
          γ * (T.card : ℝ) →
        ∃ U : Finset X.carrier,
          (((U ∆ T).card : ℝ)) ≤
            9 * (∑ x : X.carrier,
              ((((SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov
                X.generator)^[k])
                  (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)) x -
                if x ∈ T then (1 : ℝ) else 0) ^ 2) ∧
          (((U ∆ T).card : ℝ)) ≤
            72 * (SoficGroups.boundary X.generator T : ℝ) /
              ((S.card : ℝ) *
                (1 - kazhdanMarkovContractionFactor P S) ^ 2) ∧
          3 * (U ∆ T).card < T.card ∧
          (SoficGroups.boundary X.generator U : ℝ) ≤
            α * (U.card : ℝ) := by sorry
