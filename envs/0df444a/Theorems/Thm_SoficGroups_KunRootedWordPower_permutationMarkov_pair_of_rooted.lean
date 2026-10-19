-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_permutationMarkov_pair_of_rooted
-- name    : SoficGroups.KunRootedWordPower.permutationMarkov_pair_of_rooted
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/4094a5de-ab6c-4c30-94b5-be4dc265f4f1
-- title:
--   SoficGroups.KunRootedWordPower.permutationMarkov_pair_of_rooted
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

theorem SoficGroups.KunRootedWordPower.permutationMarkov_pair_of_rooted
    {G ι V : Type*} [Group G] [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (s : ι → G)
    (hgenerator : ∀ i, σ (s i) = p i)
    (q : G × G)
    (hroot : ∀ i,
      (∀ x : V, indicatorVector f x ≠ 0 →
        σ (s i * q.1) x = (σ (s i) * σ q.1) x) ∧
      (∀ x : V, indicatorVector f x ≠ 0 →
        σ (s i * q.2) x = (σ (s i) * σ q.2) x)) :
    permutationMarkov p (normalizedPairDisplacement p f σ q) =
      pairedWordAverage s (normalizedPairDisplacement p f σ) 1 q := by sorry
