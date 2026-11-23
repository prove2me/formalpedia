-- Prove2me | Theorems.Thm_P2M_KernelRank_eq_zero_of_sum_expPoly_eq_zero__c58c8e720b46
-- name    : P2M_KernelRank_eq_zero_of_sum_expPoly_eq_zero__c58c8e720b46
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:50:43.766452+00:00
-- url     : https://prove2.me/theorems/475740e6-a1ce-44c5-838a-87c6b7ff7aea
-- title:
--   P2 M Kernel Rank eq zero of sum exp Poly eq zero  c58c8e720b46: P2 M Kernel Rank eq zero of sum exp Poly eq zero  c58c8e720b46
-- statement:
--   The exponential-polynomial relation for a family of distinct rates.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RealExpPoly.lean#L16-L31
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RealExpPoly.lean#L16-L31

import Definitions.Def_KernelRankLean_ExpPoly
import Definitions.Def_KernelRankLean_RealExpPoly
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem P2M_KernelRank_eq_zero_of_sum_expPoly_eq_zero__c58c8e720b46 {κ : Type*} [Fintype κ] {ν : κ → ℂ}
    (hν : Function.Injective ν) (P : κ → ℂ[X])
    (h : ∀ u : ℝ, 0 < u → ∑ k, expPoly (P k) (ν k) u = 0) : ∀ k, P k = 0 := by sorry

alias «KernelRank».«eq_zero_of_sum_expPoly_eq_zero'» := P2M_KernelRank_eq_zero_of_sum_expPoly_eq_zero__c58c8e720b46
