-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_rooted_final_realMarkov_eq_mass_realPermutationMarkov
-- name    : SoficGroups.KunRootedWordPower.rooted_final_realMarkov_eq_mass_realPermutationMarkov
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/a3d640c7-0bec-452a-88c8-87602c5884b9
-- title:
--   SoficGroups.KunRootedWordPower.rooted_final_realMarkov_eq_mass_realPermutationMarkov
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

theorem SoficGroups.KunRootedWordPower.rooted_final_realMarkov_eq_mass_realPermutationMarkov
    {ι V : Type*} [Fintype ι]
    (p : ι → Equiv.Perm V) :
    SoficGroups.KunActualFinalRestrictedVariation.realMarkov p =
      SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov p := by sorry
