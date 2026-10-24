-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch10HM_jTripleProductPartialLaurent_eq_coe_partial_jTripleFactorPS
-- name    : QseriesFormalization.Pending.Ch10HM.jTripleProductPartialLaurent_eq_coe_partial_jTripleFactorPS
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:49:14.758836+00:00
-- url     : https://prove2.me/theorems/5d669801-b9e5-424c-8335-f09d88e1cb1c
-- title:
--   Partial triple product in $\mathbb{Q}((Q))$ equals the image of the formal power-series product
-- statement:
--   For $A<B$ and $N\in\mathbb{N}$, the finite Laurent-series product `jTripleProductPartialLaurent` $A\,B\,N=(Q^B;Q^B)_N(Q^A;Q^B)_N(Q^{B-A};Q^B)_N$ equals the image in $\mathbb{Q}((Q))$ of the power series $\prod_{n<N}(1-X^{B+Bn})(1-X^{A+Bn})(1-X^{B-A+Bn})\in\mathbb{Q}[[X]]$ (`jTripleFactorPS`). Chapter 10.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_HM.lean#L2608-L2622

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

theorem QseriesFormalization.Pending.Ch10HM.jTripleProductPartialLaurent_eq_coe_partial_jTripleFactorPS
    (A B N : ℕ) (hAB : A < B) :
    jTripleProductPartialLaurent (A : ℤ) (B : ℤ) N =
      ((∏ n ∈ Finset.range N, jTripleFactorPS ℚ A B n : ℚ⟦X⟧) : QLaurent) := by sorry
