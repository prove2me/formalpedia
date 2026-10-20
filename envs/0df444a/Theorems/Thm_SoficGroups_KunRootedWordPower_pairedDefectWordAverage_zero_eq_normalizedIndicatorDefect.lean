-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_pairedDefectWordAverage_zero_eq_normalizedIndicatorDefect
-- name    : SoficGroups.KunRootedWordPower.pairedDefectWordAverage_zero_eq_normalizedIndicatorDefect
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/3ab05368-b56b-4a46-9e80-ef064e69a817
-- title:
--   SoficGroups.KunRootedWordPower.pairedDefectWordAverage_zero_eq_normalizedIndicatorDefect
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

theorem SoficGroups.KunRootedWordPower.pairedDefectWordAverage_zero_eq_normalizedIndicatorDefect
    {G ι V : Type*} [Group G] [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (s : ι → G)
    (hone : σ 1 = 1) (hgenerator : ∀ i, σ (s i) = p i) :
    pairedDefectWordAverage s
      (normalizedPairDisplacement p f σ) 0 =
        normalizedIndicatorDefect p f := by sorry
