-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_norm_normalizedIndicatorDefect_markov_pow
-- name    : SoficGroups.KunRootedWordPower.norm_normalizedIndicatorDefect_markov_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/40023d4f-0174-42f0-8e05-5564c12447c0
-- title:
--   SoficGroups.KunRootedWordPower.norm_normalizedIndicatorDefect_markov_pow
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

theorem SoficGroups.KunRootedWordPower.norm_normalizedIndicatorDefect_markov_pow
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) (k : ℕ) :
    ‖((permutationMarkov p)^[k])
        (normalizedIndicatorDefect p f)‖ =
      ‖((permutationMarkovLinear p) ^ k)
          (permutationMarkov p (indicatorVector f) -
            indicatorVector f)‖ /
        ‖permutationMarkov p (indicatorVector f) -
          indicatorVector f‖ := by sorry
