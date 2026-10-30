-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch10HM_jCoeff_eq_window_sum
-- name    : QseriesFormalization.Pending.Ch10HM.jCoeff_eq_window_sum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:47:23.378288+00:00
-- url     : https://prove2.me/theorems/27550b95-d40f-4bd9-bd94-3235f1582386
-- title:
--   Coefficient of $Q^e$ in the theta series as a windowed signed count
-- statement:
--   For integers $a,e$ and $b>0$, `jCoeff` $a\,b\,e$ (the rational coefficient of $Q^e$ in the series $j(Q^a;Q^b)=\sum_n(-1)^nQ^{bn(n-1)/2+an}$) equals
--   $$\sum_{n=-W}^{W}\begin{cases}(-1)^n&\text{if }\mathrm{jExp}(a,b,n)=e,\\0&\text{otherwise,}\end{cases}\qquad W=4(|a|+|b|+|e|+2).$$
--   This removes the lower-support guard in the definition of `jCoeff` when $b>0$. Chapter 10.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_HM.lean#L350-L364

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

theorem QseriesFormalization.Pending.Ch10HM.jCoeff_eq_window_sum (a b e : ℤ) (hb : 0 < b) :
    jCoeff a b e =
      ∑ n ∈ Finset.Icc (-(jCoeffWindow a b e)) (jCoeffWindow a b e),
        if jExp a b n = e then negOnePowIntQ n else 0 := by sorry
