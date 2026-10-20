-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_rooted_markov_real_iterate_sq_error
-- name    : SoficGroups.KunRootedWordPower.rooted_markov_real_iterate_sq_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/f11b7741-feaa-41a1-b0c0-9953c62d089a
-- title:
--   SoficGroups.KunRootedWordPower.rooted_markov_real_iterate_sq_error
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
universe u

theorem SoficGroups.KunRootedWordPower.rooted_markov_real_iterate_sq_error
    {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq V]
    (p : ι → Equiv.Perm V) (T : Finset V) (k : ℕ) :
    ‖((permutationMarkov p)^[k])
        (indicatorVector
          (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)) -
        indicatorVector
          (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)‖ ^ 2 =
      ∑ x : V,
        ((((SoficGroups.KunFinitePermutationMarkovMass.realPermutationMarkov p)^[k])
            (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)) x -
          if x ∈ T then (1 : ℝ) else 0) ^ 2 := by sorry
