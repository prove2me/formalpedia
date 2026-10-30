-- Prove2me | Theorems.Thm_QseriesFormalization_PartIV_Ch18_legLength_staircasePartition
-- name    : QseriesFormalization.PartIV.Ch18.legLength_staircasePartition
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:47:54.792745+00:00
-- url     : https://prove2.me/theorems/a77b5dd9-938f-46a9-83bc-f9aca4e2ea6e
-- title:
--   Leg length of a cell of the staircase partition
-- statement:
--   Let $\lambda$ = `staircasePartition` $n=[n,n-1,\dots,1]$ and let $(r,c)$ be a cell of its Ferrers diagram (zero-indexed, `FerrersCell`: $r<$ length and $c<\lambda_r$). The leg length (number of lower rows containing column $c$) is
--   $$\mathrm{leg}(r,c)=n-c-(r+1)$$
--   (natural-number subtraction). Used for the staircase hook-length formula in Chapter 18.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 18. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter18.lean#L721-L746

import Definitions.Def_QseriesFormalization_Chapter18
import Mathlib

open QseriesFormalization
open QseriesFormalization.PartIV
open QseriesFormalization.PartIV.Ch18

theorem QseriesFormalization.PartIV.Ch18.legLength_staircasePartition (n r c : Nat)
    (hcell : FerrersCell (PartI.Ch04Franklin.staircasePartition n) r c) :
    legLength (PartI.Ch04Franklin.staircasePartition n) r c = n - c - (r + 1) := by sorry
