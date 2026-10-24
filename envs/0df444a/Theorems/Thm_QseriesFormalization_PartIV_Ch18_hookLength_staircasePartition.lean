-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch18_hookLength_staircasePartition
-- name    : QseriesFormalization.PartIV.Ch18.hookLength_staircasePartition
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:47:35.915066+00:00
-- url     : https://prove2.me/theorems/fffb5c31-d58c-497c-876c-a15358e2f65c
-- title:
--   Hook lengths of the staircase partition: $2(n-r-c)-1$
-- statement:
--   Let $\lambda$ = `staircasePartition` $n=[n,n-1,\dots,1]$ and let $(r,c)$ be a cell of its Ferrers diagram (zero-indexed). The hook length (arm + leg + 1) is
--   $$h(r,c)=2(n-r-c)-1$$
--   (natural-number arithmetic). This is the general hook-length formula for staircase shapes, a combinatorial computation in Chapter 18.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 18. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter18.lean#L748-L759

import Definitions.Def_QseriesFormalization_Chapter18
import Mathlib

open QseriesFormalization
open QseriesFormalization.PartIV
open QseriesFormalization.PartIV.Ch18

theorem QseriesFormalization.PartIV.Ch18.hookLength_staircasePartition (n r c : Nat)
    (hcell : FerrersCell (PartI.Ch04Franklin.staircasePartition n) r c) :
    hookLength (PartI.Ch04Franklin.staircasePartition n) r c = 2 * (n - r - c) - 1 := by sorry
