-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch10HM_lcoeff_qPochhammer_mul_gaussian_center_sub_low_nat
-- name    : QseriesFormalization.Pending.Ch10HM.lcoeff_qPochhammer_mul_gaussian_center_sub_low_nat
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:51:07.860679+00:00
-- url     : https://prove2.me/theorems/9947a5ac-fbbe-443b-befa-509f8c3b64d3
-- title:
--   Low-order coefficients of $(q;q)_N\binom{2N}{N-r}_q$, $q=Q^b$ (natural exponents)
-- statement:
--   Let $b,N,r,k\in\mathbb{N}$ with $b>0$, $r\le N$ and $k<b(N-r+1)$. In $\mathbb{Q}((Q))$, with $q=Q^b$, the coefficient of $Q^k$ in $(q;q)_N\binom{2N}{N-r}_q$ is $1$ if $k=0$ and $0$ otherwise. So this series equals $1$ modulo $Q^{b(N-r+1)}$. Chapter 10.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_HM.lean#L2117-L2142

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

theorem QseriesFormalization.Pending.Ch10HM.lcoeff_qPochhammer_mul_gaussian_center_sub_low_nat
    (b N r k : ℕ) (hb : 0 < b) (hr : r ≤ N)
    (hk : k < b * (N - r + 1)) :
    lcoeff
        (qPochhammer (Qpow (b : ℤ)) N *
          gaussianBinom (Qpow (b : ℤ)) (2 * N) (N - r))
        (k : ℤ) =
      if k = 0 then 1 else 0 := by sorry
