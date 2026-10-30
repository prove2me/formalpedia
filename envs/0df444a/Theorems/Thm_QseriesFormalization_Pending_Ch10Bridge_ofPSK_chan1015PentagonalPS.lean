-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch10Bridge_ofPSK_chan1015PentagonalPS
-- name    : QseriesFormalization.Pending.Ch10Bridge.ofPSK_chan1015PentagonalPS
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:45:57.165319+00:00
-- url     : https://prove2.me/theorems/da4799f0-c2ab-45ae-9257-2b8c8b4d2ce2
-- title:
--   The pentagonal power series for Chan (10.15) maps to the Laurent series `kP10`
-- statement:
--   Let `chan1015PentagonalPS` be the power series over $\mathbb{Q}$ obtained from $\sum_{k\in\mathbb{Z}}(-1)^kX^{(5k^2-3k)/2}$ by the substitution $X\mapsto X^3$ (so $q=Q^3$). The statement: its image under `ofPSK` (the embedding $\mathbb{Q}[[X]]\to\mathbb{Q}((Q))$, $X\mapsto Q$) equals `kP10`, the right-hand side series of the identity in $\mathbb{Q}((Q))$ defined as a sum of a family of theta terms. A bridge step in Chapter 10 (tenth-order mock theta function identities).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_Bridge.lean#L169-L227

import Definitions.Def_QseriesFormalization_Pending_Chapter10_TenthOrder
import Definitions.Def_QseriesFormalization_Pending_Chapter10_TwoVar
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

open scoped Classical
open QseriesFormalization
open QseriesFormalization.Ch10TwoVar
open QseriesFormalization.Pending.Ch10TenthOrder
open QseriesFormalization.Pending.JTPFormalPSPentagonal

open QseriesFormalization QseriesFormalization.Pending

/-! ## Sign helper: `negOnePowInt R k = (-1)^k` as a `zpow` -/

/-! ## `squareWindow` capture: `m² ≤ N ⟹ m ≤ squareWindow N` -/

/-! ## B-RHS (pentagonal): `ofPSK chan1015PentagonalPS = kP10` -/

theorem QseriesFormalization.Pending.Ch10Bridge.ofPSK_chan1015PentagonalPS : ofPSK chan1015PentagonalPS = kP10 := by sorry
