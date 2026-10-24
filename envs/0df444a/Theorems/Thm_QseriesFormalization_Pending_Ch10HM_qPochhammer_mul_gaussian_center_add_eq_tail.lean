-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch10HM_qPochhammer_mul_gaussian_center_add_eq_tail
-- name    : QseriesFormalization.Pending.Ch10HM.qPochhammer_mul_gaussian_center_add_eq_tail
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:51:48.192232+00:00
-- url     : https://prove2.me/theorems/1ff9aed8-b7bc-40cc-9731-cdc085ad84c5
-- title:
--   Tail form of $(q;q)_N\binom{2N}{N+r}_q$ with $q=Q^b$ in $\mathbb{Q}((Q))$
-- statement:
--   In the Laurent series field $\mathbb{Q}((Q))$, let $q=Q^b$ with $b>0$, and $0\le r\le N$. Then
--   $$(q;q)_N\binom{2N}{N+r}_q=(q^{N-r+1};q)_r\,(q^{N+r+1};q)_{N-r},$$
--   where $(a;q)_n=\prod_{k<n}(1-aq^k)$. Both sides are products of factors $(1-Q^{bm})$, which gives low-order coefficient information (see the next lemmas). Chapter 10.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_HM.lean#L1972-L2013

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

theorem QseriesFormalization.Pending.Ch10HM.qPochhammer_mul_gaussian_center_add_eq_tail
    (b N r : ℕ) (hb : 0 < b) (hr : r ≤ N) :
    qPochhammer (Qpow (b : ℤ)) N *
        gaussianBinom (Qpow (b : ℤ)) (2 * N) (N + r) =
      qPoch ((Qpow (b : ℤ)) * (Qpow (b : ℤ)) ^ (N - r))
          (Qpow (b : ℤ)) r *
        qPoch ((Qpow (b : ℤ)) * (Qpow (b : ℤ)) ^ (N + r))
          (Qpow (b : ℤ)) (N - r) := by sorry
