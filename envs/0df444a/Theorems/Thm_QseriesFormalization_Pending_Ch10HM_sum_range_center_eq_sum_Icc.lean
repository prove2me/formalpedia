-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch10HM_sum_range_center_eq_sum_Icc
-- name    : QseriesFormalization.Pending.Ch10HM.sum_range_center_eq_sum_Icc
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:52:15.23373+00:00
-- url     : https://prove2.me/theorems/f081fe25-c16e-457a-b4e6-fb01af767739
-- title:
--   Re-centering a finite sum: $\sum_{k<2N+1}F(k-N)=\sum_{n=-N}^{N}F(n)$
-- statement:
--   Let $M$ be an additive commutative monoid, $F:\mathbb{Z}\to M$ and $N\in\mathbb{N}$. Then $\sum_{k=0}^{2N}F(k-N)=\sum_{n=-N}^{N}F(n)$. A reindexing lemma for finite Jacobi-triple-product sums in Chapter 10.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_HM.lean#L2435-L2488

import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Log.Summable

namespace QseriesFormalization.Pending.JTPFormalPSPentagonal end QseriesFormalization.Pending.JTPFormalPSPentagonal

/-!
# Chapter 10 HM core

This is the sorry-free core of `Chapter10_HM` needed by `Chapter10_TwoVar`, extracted
verbatim from the pinned source `Pending/Chapter10_HM.lean` at the HM line ranges
38-74, 81-86, 95-116, 125-165, 180-198, 215-384, 674-824, 857-863, 867-885, 889-894, 954-1037, 1052-1115, 1836-2313, 2333-2698, 2702-2716, 2727-2748, 2763-2774, 3168-3173, 3273-3283, 3369-3389, 3413-3442, 3449-3463, 3511-3518, 3535-3548, 3861-3873, 3879-3894.
The unfinished second HM route (with its two open goals) stays in `Chapter10_HM`,
which is not part of the port.
-/

open scoped LaurentSeries
open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.Pending.JTPFormalPSPentagonal

theorem QseriesFormalization.Pending.Ch10HM.sum_range_center_eq_sum_Icc {M : Type*} [AddCommMonoid M]
    (F : ℤ → M) (N : ℕ) :
    (∑ k ∈ Finset.range (2 * N + 1), F ((k : ℤ) - (N : ℤ))) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), F n := by sorry
