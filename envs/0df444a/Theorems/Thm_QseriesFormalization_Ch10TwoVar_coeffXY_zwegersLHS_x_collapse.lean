-- Prove2me | Theorems.Thm_QseriesFormalization_Ch10TwoVar_coeffXY_zwegersLHS_x_collapse
-- name    : QseriesFormalization.Ch10TwoVar.coeffXY_zwegersLHS_x_collapse
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:57:32.288654+00:00
-- url     : https://prove2.me/theorems/6731b5eb-0c31-45f8-9d4e-18e2c6aace58
-- title:
--   Circle-sum collapse of the $x^l$-slice of the Zwegers lattice sum
-- statement:
--   Let $L$ be the weighted lattice sum $\sum_{k,l}(-1)^{k+l}(\delta(k)-\delta(l))Q^{k^2+l^2}x^l$ with $\delta(k)=1$ if $3\mid k$ and $0$ otherwise (`zwegersLHS_x`). For integers $l,a$, the coefficient of $Q^a$ in the $x^l$-slice of $L$ equals the finite sum $\sum_{k\in\mathbb{Z}:\ k^2+l^2=a}(-1)^{k+l}(\delta(k)-\delta(l))$ (a sum over lattice points on a circle). Chapter 10.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_TwoVar.lean#L1829-L1866

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

/-! ### Plane-support infrastructure (`y⁰`- and `x⁰`-supported series) -/

/-! ### The Zwegers RHS and the main identity (Lemma 10.1, `x`-version)

We state Zwegers' Lemma 10.1 in the `poch_q2`-cleared form
`embedQ poch_q2 · LHS = - (Q x⁻¹) · embedQ poch_q · Θ(x;q²) · Θ(x;q)`
(verified numerically; design `chan3-Ch10-twovar-source-route.md`).  `thetaX_q := thetaMon 3 0 1 0`,
`thetaX_q2 := thetaMon 6 0 1 0`. -/

/-! The five irreducible analytic inputs of Zwegers' proof (Chen Eq. 10.34–10.38), each a
one-variable `K`-identity / per-slice functional equation, numerically verified in
`chan3-Ch10-twovar-source-route.md` and `/tmp/zwfe.py`.  These are the genuinely-resistant
pieces (per the design's flagged candidates), isolated as documented `sorry`s with their
exact statements; everything that consumes them is proved unconditionally. -/

/-! ### General one-variable `K`-theta objects `J(z;Q^A)` and the Zwegers slice reductions

We reduce both slices `coeffXY zwegersLHS_x j 0` (`j=0,1,2`) and
`coeffXY (thetaX_q2*thetaX_q) m 0` (`m=1,2,3`) to one-variable theta sums
`J = ∑'_r single (A·T r + e·r) (w r)` (a `K`-element), then to the two product
identities `P0`/`P12`. -/

theorem QseriesFormalization.Ch10TwoVar.coeffXY_zwegersLHS_x_collapse (l a : ℤ) :
    (coeffXY zwegersLHS_x l 0).coeff a
      = ∑ᶠ k : ℤ, (if k ^ 2 + l ^ 2 = a then zW k l else 0) := by sorry
