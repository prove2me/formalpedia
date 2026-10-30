-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch10HM_lcoeff_jTripleProductPartialLaurent_eq_jCoeff_succ_degree
-- name    : QseriesFormalization.Pending.Ch10HM.lcoeff_jTripleProductPartialLaurent_eq_jCoeff_succ_degree
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:49:33.799994+00:00
-- url     : https://prove2.me/theorems/40a82238-70b4-47aa-bc0f-3b5e99bd0ab6
-- title:
--   Partial triple product with $d+1$ factors has the correct $Q^d$ coefficient ($0<A<B$)
-- statement:
--   Let $A,B,d\in\mathbb{N}$ with $0<A<B$. Let $P_{d+1}$ be the finite triple product $(Q^B;Q^B)_{d+1}(Q^A;Q^B)_{d+1}(Q^{B-A};Q^B)_{d+1}\in\mathbb{Q}((Q))$ (`jTripleProductPartialLaurent`). Then the coefficient of $Q^d$ in $P_{d+1}$ equals `jCoeff` $A\,B\,d$, the coefficient of $Q^d$ in the theta series $j(Q^A;Q^B)=\sum_n(-1)^nQ^{Bn(n-1)/2+An}$. A coefficient form of the Jacobi triple product used in Chapter 10.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_HM.lean#L2525-L2606

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

open QseriesFormalization.Pending.Ch10HM.ZQuad

theorem QseriesFormalization.Pending.Ch10HM.lcoeff_jTripleProductPartialLaurent_eq_jCoeff_succ_degree
    (A B d : ℕ) (hA : 0 < A) (hAB : A < B) :
    lcoeff (jTripleProductPartialLaurent (A : ℤ) (B : ℤ) (d + 1)) (d : ℤ) =
      jCoeff (A : ℤ) (B : ℤ) (d : ℤ) := by sorry
