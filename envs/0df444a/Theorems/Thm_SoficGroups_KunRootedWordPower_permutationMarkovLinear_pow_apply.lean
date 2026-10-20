-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_permutationMarkovLinear_pow_apply
-- name    : SoficGroups.KunRootedWordPower.permutationMarkovLinear_pow_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/055f8666-8046-4133-ad31-821ad1fb5390
-- title:
--   SoficGroups.KunRootedWordPower.permutationMarkovLinear_pow_apply
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

theorem SoficGroups.KunRootedWordPower.permutationMarkovLinear_pow_apply
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (k : ℕ)
    (x : EuclideanSpace ℂ V) :
    ((permutationMarkovLinear p) ^ k) x =
      ((permutationMarkov p)^[k]) x := by sorry
