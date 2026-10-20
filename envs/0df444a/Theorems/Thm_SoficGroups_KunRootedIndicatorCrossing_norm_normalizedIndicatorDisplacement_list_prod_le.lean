-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_norm_normalizedIndicatorDisplacement_list_prod_le
-- name    : SoficGroups.KunRootedIndicatorCrossing.norm_normalizedIndicatorDisplacement_list_prod_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:24.345557+00:00
-- url     : https://prove2.me/theorems/cdcad1dc-ce42-4667-a53a-98d11cef5907
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.norm_normalizedIndicatorDisplacement_list_prod_le
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

theorem SoficGroups.KunRootedIndicatorCrossing.norm_normalizedIndicatorDisplacement_list_prod_le
    {ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hdefect : permutationMarkov p (indicatorVector f) ≠
      indicatorVector f) (w : List ι) :
    ‖normalizedIndicatorDisplacement p f (w.map p).prod‖ ≤
      (Fintype.card ι : ℝ) * w.length := by sorry
