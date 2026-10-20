-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_RootedIndicatorMarkovModel_IsRootedAtRadius_mono
-- name    : SoficGroups.KunRootedWordPower.RootedIndicatorMarkovModel.IsRootedAtRadius.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/0c817877-bd29-43e9-b863-d8b7b9c83ecf
-- title:
--   SoficGroups.KunRootedWordPower.RootedIndicatorMarkovModel.IsRootedAtRadius.mono
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

theorem SoficGroups.KunRootedWordPower.RootedIndicatorMarkovModel.IsRootedAtRadius.mono
    {G ι : Type u} [Group G]
    {X : RootedIndicatorMarkovModel G ι}
    {w : G → List ι} {r R : ℕ}
    (h : X.IsRootedAtRadius w R) (hr : r ≤ R) :
    X.IsRootedAtRadius w r := by sorry
