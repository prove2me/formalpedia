-- Prove2me | Theorems.Thm_QseriesFormalization_Ch10TwoVar_jacobi_derivative_poch_cube
-- name    : QseriesFormalization.Ch10TwoVar.jacobi_derivative_poch_cube
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T09:00:53.302802+00:00
-- url     : https://prove2.me/theorems/591d47ee-388f-48e6-8f18-96937cc8d563
-- title:
--   Jacobi's derivative identity rescaled: $-\sum_t(-1)^t\,t\,Q^{3T(t)}=(Q^3;Q^3)_\infty^3$
-- statement:
--   In $K=\mathbb{Q}((Q))$, with $T(t)=t(t-1)/2$,
--   $$-\sum_{t\in\mathbb{Z}}(-1)^t\,t\,Q^{3T(t)}=(Q^3;Q^3)_\infty^{3}.$$
--   This is Jacobi's identity $(q;q)_\infty^3=\sum(-1)^k(2k+1)q^{k(k+1)/2}$ in derivative form, with $q=Q^3$ (`poch_q` $=(Q^3;Q^3)_\infty$). Used in Chapter 10.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_TwoVar.lean#L1142-L1214

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
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Summable

open scoped Classical
open Set

open QseriesFormalization
open QseriesFormalization.Ch10TwoVar

/-! ## Layer A — the q-first lexicographic Hahn kernel -/

/-! ### The q-slice `coeffXY` -/

/-! ### The Q-embedding `embedQ : K →+* S` -/

/-! ## Layer B — integer quadratic helpers -/

/-! ## Layer C — `thetaMon` as the hsum of a summable family -/

/-! ### Symmetry specials -/

/-! ## Layer D — q-Pochhammer bridge

We import the committed formal-power-series infrastructure (`qPochInfPS`, the cube
identity `qPochInfPS^3 = jacobiThetaPS`) and transport it into `K = ℚ((Q))` via
`HahnSeries.ofPowerSeries` composed with `PowerSeries.expand` (the `q = Q^3` rescaling).
-/

open QseriesFormalization.PartIV.Ch19 (qPochInfPS jacobiThetaPS jacobiTripleSign
  )

/-! ### A `K`-level theta summable family

The one-variable theta sums `∑' t, single (3·T t) (w t)` (in `K = ℚ((Q))`) needed for
`theta_one_zero` and the Jacobi derivative.  The Q-degree `3·T t = thetaQDeg 3 0 t` is
bounded below with finite fibers (reusing the layer-C bounds), so the family is summable. -/

/-! ### Jacobi's derivative identity `-∑ (-1)^t t q^{T t} = (q;q)_∞^3` -/

/-! ### Jacobi's derivative identity, finished -/

theorem QseriesFormalization.Ch10TwoVar.jacobi_derivative_poch_cube :
    - (kTheta (fun t => (-1) ^ t * t)) = poch_q ^ 3 := by sorry
