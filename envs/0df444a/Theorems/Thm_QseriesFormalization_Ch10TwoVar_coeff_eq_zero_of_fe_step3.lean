-- Prove2me | Theorems.Thm_QseriesFormalization_Ch10TwoVar_coeff_eq_zero_of_fe_step3
-- name    : QseriesFormalization.Ch10TwoVar.coeff_eq_zero_of_fe_step3
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:58:17.984874+00:00
-- url     : https://prove2.me/theorems/43da8860-1e9a-484c-acce-b1f7f43eea40
-- title:
--   Uniqueness: the step-3 recurrence with $a(0)=a(1)=a(2)=0$ forces $a\equiv0$
-- statement:
--   Let $a:\mathbb{Z}\to K=\mathbb{Q}((Q))$ satisfy $a(n+3)=-Q^{6n+9}\,a(n)$ for all $n$ and $a(0)=a(1)=a(2)=0$. Then $a(n)=0$ for all $n\in\mathbb{Z}$ (write $n=r+3t$ with $r\in\{0,1,2\}$ and apply the closed form). This is the uniqueness step in the proof of Zwegers' Lemma 10.1, Chapter 10.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_TwoVar.lean#L1374-L1393

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

/-! ## Layer E — Zwegers Lemma 10.1 (functional-equation route)

The classical identity (Chen, Eq. 10.34; Zwegers 2010, Lemma 3.1)
`∑_{k,l} (-1)^{k+l}(δ(k)-δ(l)) q^{(k²+l²)/3} x^l = -x⁻¹q^{1/3} (q²;q²)∞/(q;q)∞ Θ(x;q²)Θ(x;q)`,
proved here in the `poch_q2`-cleared form to avoid `K`-division.
-/

/-! ### The 2D summable family for the Zwegers LHS

Q-degree `k²+l²` is bounded below by `0` with finite fibers (lattice points on a
circle), so the family indexed by `ℤ × ℤ` is summable in `S`. -/

/-! ### Uniqueness from the step-3 functional equation -/

theorem QseriesFormalization.Ch10TwoVar.coeff_eq_zero_of_fe_step3 (a : ℤ → K)
    (hrec : ∀ n, a (n + 3) = - Qpow (6 * n + 9) * a n)
    (h0 : a 0 = 0) (h1 : a 1 = 0) (h2 : a 2 = 0) :
    ∀ n, a n = 0 := by sorry
