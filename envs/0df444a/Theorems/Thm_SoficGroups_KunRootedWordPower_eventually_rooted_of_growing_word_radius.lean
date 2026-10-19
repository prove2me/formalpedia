-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_eventually_rooted_of_growing_word_radius
-- name    : SoficGroups.KunRootedWordPower.eventually_rooted_of_growing_word_radius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/ae5ac2a5-4ed0-498f-a889-04df4f81ecf8
-- title:
--   SoficGroups.KunRootedWordPower.eventually_rooted_of_growing_word_radius
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

theorem SoficGroups.KunRootedWordPower.eventually_rooted_of_growing_word_radius
    {G ι : Type u} [Group G]
    (X : ℕ → RootedIndicatorMarkovModel G ι)
    (w : G → List ι)
    (hroot : ∀ n, (X n).IsRootedAtRadius w n)
    (a g : G) :
    ∀ᶠ n in Filter.atTop,
      ∀ x : (X n).carrier,
        indicatorVector (X n).indicator x ≠ 0 →
          (X n).evaluation (a * g) x =
            ((X n).evaluation a * (X n).evaluation g) x := by sorry
