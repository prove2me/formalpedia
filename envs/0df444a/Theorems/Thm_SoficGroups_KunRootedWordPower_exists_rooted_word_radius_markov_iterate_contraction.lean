-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_exists_rooted_word_radius_markov_iterate_contraction
-- name    : SoficGroups.KunRootedWordPower.exists_rooted_word_radius_markov_iterate_contraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/040d63cf-0fef-49f9-8879-f59812cf45b1
-- title:
--   SoficGroups.KunRootedWordPower.exists_rooted_word_radius_markov_iterate_contraction
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
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w

theorem SoficGroups.KunRootedWordPower.exists_rooted_word_radius_markov_iterate_contraction
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℕ, ∀ X : RootedIndicatorMarkovModel G ↥S,
      X.IsGenerated (fun i : ↥S => (i : G)) w →
      X.IsRootedAtRadius w r →
      ‖((permutationMarkov X.generator)^[k + 1])
            (indicatorVector X.indicator) -
          ((permutationMarkov X.generator)^[k])
            (indicatorVector X.indicator)‖ ≤
        (kazhdanMarkovContractionFactor P S ^ k + ε) *
          ‖permutationMarkov X.generator
              (indicatorVector X.indicator) -
            indicatorVector X.indicator‖ := by sorry
