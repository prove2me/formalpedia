-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch10Bridge_mem_squareWindow_Icc
-- name    : QseriesFormalization.Pending.Ch10Bridge.mem_squareWindow_Icc
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:45:46.634211+00:00
-- url     : https://prove2.me/theorems/a32e84b7-dd6f-46d7-8138-8c123d7e4e6e
-- title:
--   Square window: $k^2\le N$ implies $|k|\le\mathrm{squareWindow}(N)$
-- statement:
--   For $N\in\mathbb{N}$ and $k\in\mathbb{Z}$ with $k^2\le N$, we have $-w\le k\le w$ where $w=$ `squareWindow` $N$ is the largest $m\le N$ with $m^2\le N$. A box-bound lemma for the finite sums in Chapter 10 (tenth-order mock theta function identities).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_Bridge.lean#L85-L97

import Definitions.Def_QseriesFormalization_Pending_Chapter10_TenthOrder
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Summable

namespace QseriesFormalization.Ch10TwoVar end QseriesFormalization.Ch10TwoVar

open scoped Classical
open QseriesFormalization
open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10TenthOrder
open QseriesFormalization.Pending.JTPFormalPSPentagonal

open QseriesFormalization QseriesFormalization.Pending

/-! ## Sign helper: `negOnePowInt R k = (-1)^k` as a `zpow` -/

/-! ## `squareWindow` capture: `m² ≤ N ⟹ m ≤ squareWindow N` -/

theorem QseriesFormalization.Pending.Ch10Bridge.mem_squareWindow_Icc {N : ℕ} {k : ℤ} (h : k ^ 2 ≤ (N : ℤ)) :
    -(squareWindow N : ℤ) ≤ k ∧ k ≤ (squareWindow N : ℤ) := by sorry
