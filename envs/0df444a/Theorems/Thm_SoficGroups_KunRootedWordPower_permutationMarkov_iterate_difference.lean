-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_permutationMarkov_iterate_difference
-- name    : SoficGroups.KunRootedWordPower.permutationMarkov_iterate_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/c57f9998-f5c1-4c1f-ad72-6c6b3c4d7556
-- title:
--   SoficGroups.KunRootedWordPower.permutationMarkov_iterate_difference
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

theorem SoficGroups.KunRootedWordPower.permutationMarkov_iterate_difference
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (x : EuclideanSpace ℂ V)
    (k : ℕ) :
    ((permutationMarkov p)^[k + 1]) x -
        ((permutationMarkov p)^[k]) x =
      ((permutationMarkovLinear p) ^ k)
        (permutationMarkov p x - x) := by sorry
