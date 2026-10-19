-- Prove2me | Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_ofKernel_kerFun_one_eq_coe_single
-- name    : SoficGroups.KunRootedIndicatorCrossing.ofKernel_kerFun_one_eq_coe_single
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/bb6144d3-dcc2-4f28-aed0-b2d029dafc68
-- title:
--   SoficGroups.KunRootedIndicatorCrossing.ofKernel_kerFun_one_eq_coe_single
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

theorem SoficGroups.KunRootedIndicatorCrossing.ofKernel_kerFun_one_eq_coe_single
    {I : Type u} (L : Matrix I I (ℂ →L[ℂ] ℂ))
    [Fact L.PosSemidef] (i : I) :
    RKHS.kerFun (RKHS.OfKernel L) i (1 : ℂ) =
      ((Finsupp.single (i, (1 : ℂ)) (1 : ℂ) : RKHS.H₀ L) :
        RKHS.OfKernel L) := by sorry
