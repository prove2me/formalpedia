-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_exists_rooted_word_radius_all_markov_iterate_contractions
-- name    : SoficGroups.KunRootedWordPower.exists_rooted_word_radius_all_markov_iterate_contractions
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/bb47eb14-f5e3-45d7-998b-5300a44bf667
-- title:
--   SoficGroups.KunRootedWordPower.exists_rooted_word_radius_all_markov_iterate_contractions
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
universe u v

theorem SoficGroups.KunRootedWordPower.exists_rooted_word_radius_all_markov_iterate_contractions
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
      ∀ j ≤ k,
        ‖((permutationMarkov X.generator)^[j + 1])
              (indicatorVector X.indicator) -
            ((permutationMarkov X.generator)^[j])
              (indicatorVector X.indicator)‖ ≤
          (kazhdanMarkovContractionFactor P S ^ j + ε) *
            ‖permutationMarkov X.generator
                (indicatorVector X.indicator) -
              indicatorVector X.indicator‖ := by sorry
