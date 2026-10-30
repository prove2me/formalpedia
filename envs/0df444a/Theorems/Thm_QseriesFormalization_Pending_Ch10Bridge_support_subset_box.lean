-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch10Bridge_support_subset_box
-- name    : QseriesFormalization.Pending.Ch10Bridge.support_subset_box
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:46:22.882488+00:00
-- url     : https://prove2.me/theorems/97109130-09c6-4108-93b0-a581df009ec7
-- title:
--   Support of the $q^m$ part of Chan's quadruple sum lies in an explicit box
-- statement:
--   For $m\in\mathbb{N}$, consider $(k,l,r,s)\in(\mathbb{Z}\times\mathbb{Z})\times(\mathbb{Z}\times\mathbb{Z})$ and the function that returns the rational coefficient `quadCoeff` $k\,l\,r\,s$ when the exponent $k^2+l^2+r^2+3rs+s^2+3r+3s+1$ (`qExp4`) equals $m$, and $0$ otherwise. Its support is contained in the finite box `chan1015Box` $m$: $|k|,|l|\le\mathrm{squareWindow}(m)$ and $|r|,|s|\le m+2$. A finiteness lemma for the quadruple sum in Chapter 10 (tenth-order mock theta function identities).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_Bridge.lean#L305-L352

import Definitions.Def_QseriesFormalization_Pending_Chapter10_TwoVar
import Definitions.Def_QseriesFormalization_Pending_Chapter10_Bridge
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

open QseriesFormalization QseriesFormalization.Pending QseriesFormalization.Pending.Ch10Bridge

/-! ## Sign helper: `negOnePowInt R k = (-1)^k` as a `zpow` -/

/-! ## `squareWindow` capture: `m² ≤ N ⟹ m ≤ squareWindow N` -/

/-! ## B-RHS (pentagonal): `ofPSK chan1015PentagonalPS = kP10` -/

/-! ## B-LHS: `ofPSK (chan1015LHSPS ℚ) = ChanQuadSum` -/

theorem QseriesFormalization.Pending.Ch10Bridge.support_subset_box (m : ℕ) :
    (Function.support fun p : (ℤ × ℤ) × (ℤ × ℤ) =>
        if qExp4 p.1.1 p.1.2 p.2.1 p.2.2 = (m : ℤ) then quadCoeff p.1.1 p.1.2 p.2.1 p.2.2 else 0)
      ⊆ (chan1015Box m : Set ((ℤ × ℤ) × (ℤ × ℤ))) := by sorry
