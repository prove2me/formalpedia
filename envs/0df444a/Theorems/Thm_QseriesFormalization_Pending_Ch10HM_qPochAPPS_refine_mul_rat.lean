-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch10HM_qPochAPPS_refine_mul_rat
-- name    : QseriesFormalization.Pending.Ch10HM.qPochAPPS_refine_mul_rat
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:51:44.122569+00:00
-- url     : https://prove2.me/theorems/24a80d99-f7f4-43a6-92d0-8bb5f88d7492
-- title:
--   Refining an arithmetic-progression product: $(X^r;X^m)_\infty=\prod_{i<k}(X^{r+mi};X^{mk})_\infty$
-- statement:
--   For natural numbers $r,m,k$ with $m>0$ and $k\ne0$, in $\mathbb{Q}[[X]]$,
--   $$(X^r;X^m)_\infty=\prod_{i=0}^{k-1}(X^{r+mi};X^{mk})_\infty,$$
--   where $(X^a;X^m)_\infty=\prod_{n\ge0}(1-X^{a+mn})$ (`qPochAPPS`). It splits the progression modulo $m$ into $k$ progressions modulo $mk$. Chapter 10.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_HM.lean#L2727-L2748

import Definitions.Def_QseriesFormalization_DefCoreQSeries
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

open scoped LaurentSeries
open Filter
open PowerSeries
open scoped Topology PowerSeries PowerSeries.WithPiTopology
open QseriesFormalization.Pending.JTPFormalPSPentagonal

theorem QseriesFormalization.Pending.Ch10HM.qPochAPPS_refine_mul_rat (r m k : ℕ) (hm : 0 < m) (hk : k ≠ 0) :
    qPochAPPS ℚ r m =
      ∏ i : Fin k, qPochAPPS ℚ (r + m * i.val) (m * k) := by sorry
