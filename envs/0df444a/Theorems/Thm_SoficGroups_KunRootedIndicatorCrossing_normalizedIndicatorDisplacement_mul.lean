-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_normalizedIndicatorDisplacement_mul
-- name    : SoficGroups.KunRootedIndicatorCrossing.normalizedIndicatorDisplacement_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/e87e40eb-39ed-4df5-ace5-b0afd4d5735e
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.normalizedIndicatorDisplacement_mul
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology

theorem SoficGroups.KunRootedIndicatorCrossing.normalizedIndicatorDisplacement_mul
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (q r : Equiv.Perm V) :
    normalizedIndicatorDisplacement p f (q * r) =
      normalizedIndicatorDisplacement p f q +
        permutationUnitary q (normalizedIndicatorDisplacement p f r) := by sorry
