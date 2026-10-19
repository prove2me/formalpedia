-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_rooted_indicator_defect_sq_le_boundary
-- name    : SoficGroups.KunRootedWordPower.rooted_indicator_defect_sq_le_boundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/4e5bdd22-1e33-440e-bb70-14da15906a90
-- title:
--   SoficGroups.KunRootedWordPower.rooted_indicator_defect_sq_le_boundary
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

theorem SoficGroups.KunRootedWordPower.rooted_indicator_defect_sq_le_boundary
    {ι V : Type*} [Fintype ι] [Nonempty ι]
    [Fintype V] [DecidableEq V]
    (p : ι → Equiv.Perm V) (T : Finset V) :
    ‖permutationMarkov p
        (indicatorVector
          (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)) -
        indicatorVector
          (SoficGroups.KunFinitePermutationMarkovMass.realIndicator T)‖ ^ 2 ≤
      2 * (SoficGroups.boundary p T : ℝ) /
        (Fintype.card ι : ℝ) := by sorry
