-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch10HM_two_mul_jExp
-- name    : QseriesFormalization.Pending.Ch10HM.two_mul_jExp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:52:57.078255+00:00
-- url     : https://prove2.me/theorems/7542ed38-6841-4808-b959-007086c7a9c2
-- title:
--   $2\cdot\mathrm{jExp}(a,b,n)=\mathrm{jExpTwice}(a,b,n)$
-- statement:
--   For integers $a,b,n$, with $\mathrm{jExp}(a,b,n)=\lfloor bn(n-1)/2\rfloor+an$ (the exponent of the $n$-th term of the theta series $j(Q^a;Q^b)=\sum_n(-1)^nQ^{bn(n-1)/2+an}$) and $\mathrm{jExpTwice}(a,b,n)=bn(n-1)+2an$, we have $2\,\mathrm{jExp}(a,b,n)=\mathrm{jExpTwice}(a,b,n)$ (the integer division is exact since $n(n-1)$ is even). Chapter 10 bookkeeping.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_HM.lean#L215-L227

import Definitions.Def_QseriesFormalization_Pending_Chapter10_HMCore
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Chapter 10 HM core

This is the sorry-free core of `Chapter10_HM` needed by `Chapter10_TwoVar`, extracted
verbatim from the pinned source `Pending/Chapter10_HM.lean` at the HM line ranges
38-74, 81-86, 95-116, 125-165, 180-198, 215-384, 674-824, 857-863, 867-885, 889-894, 954-1037, 1052-1115, 1836-2313, 2333-2698, 2702-2716, 2727-2748, 2763-2774, 3168-3173, 3273-3283, 3369-3389, 3413-3442, 3449-3463, 3511-3518, 3535-3548, 3861-3873, 3879-3894.
The unfinished second HM route (with its two open goals) stays in `Chapter10_HM`,
which is not part of the port.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.Ch10HM

open scoped LaurentSeries
open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.Pending.JTPFormalPSPentagonal

theorem QseriesFormalization.Pending.Ch10HM.two_mul_jExp (a b n : ℤ) :
    2 * jExp a b n = jExpTwice a b n := by sorry
