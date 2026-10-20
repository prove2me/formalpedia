-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_eventually_permutationMarkov_pair_of_rooted
-- name    : SoficGroups.KunRootedWordPower.eventually_permutationMarkov_pair_of_rooted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/94daba31-1d06-4f49-8572-e2baa40e241e
-- title:
--   SoficGroups.KunRootedWordPower.eventually_permutationMarkov_pair_of_rooted
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

theorem SoficGroups.KunRootedWordPower.eventually_permutationMarkov_pair_of_rooted
    {G ι : Type*} [Group G] [Fintype ι]
    {V : ℕ → Type*} [∀ n, Fintype (V n)]
    (p : ∀ n, ι → Equiv.Perm (V n))
    (f : ∀ n, V n → ℝ)
    (σ : ∀ n, G → Equiv.Perm (V n))
    (s : ι → G)
    (hgenerator : ∀ n i, σ n (s i) = p n i)
    (hroot : ∀ a g : G, ∀ᶠ n in Filter.atTop,
      ∀ x : V n, indicatorVector (f n) x ≠ 0 →
        σ n (a * g) x = (σ n a * σ n g) x)
    (q : G × G) :
    ∀ᶠ n in Filter.atTop,
      permutationMarkov (p n)
        (normalizedPairDisplacement (p n) (f n) (σ n) q) =
        pairedWordAverage s
          (normalizedPairDisplacement (p n) (f n) (σ n)) 1 q := by sorry
