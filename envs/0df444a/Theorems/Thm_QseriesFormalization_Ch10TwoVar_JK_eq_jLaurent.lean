-- Prove2me | Theorems.Thm_QseriesFormalization_Ch10TwoVar_JK_eq_jLaurent
-- name    : QseriesFormalization.Ch10TwoVar.JK_eq_jLaurent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T08:52:25.465264+00:00
-- url     : https://prove2.me/theorems/d1f5d7d8-f057-4d92-a895-8148613d106a
-- title:
--   Alternating theta bridge: $\mathrm{JK}_{b,a}((-1)^r)=j(Q^a;Q^b)$ for $0<a<b$
-- statement:
--   For integers $a,b$ with $0<a<b$, the two-variable-framework theta element `JK` $b\,a$ with weights $w(r)=(-1)^r$ (the $\mathbb{Q}((Q))$-sum $\sum_r(-1)^rQ^{bT(r)+ar}$, with $T(r)$ the triangular-type exponent) equals the coefficient-defined theta series `jLaurent` $a\,b$. A bridge between two formulations of the same theta function, Chapter 10.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_TwoVar.lean#L2331-L2356

import Definitions.Def_QseriesFormalization_Pending_Chapter10_HMCore
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

/-! ### Layer F — K-level arithmetic-progression `q`-Pochhammer products

We transport the committed formal-power-series AP product `qPochAPPS ℚ r m = (X^r;X^m)_∞`
(`JTPFormalPSPentagonal`) into `K = ℚ((Q))` via the ring map `ofPSK` (`X ↦ Q`), obtaining the
infinite products `apK r m = (Q^r;Q^m)_∞` and (with the `(1+X^…)` factors) the signed variants.
The single-factor coefficient-stabilization lemma `coeff_mul_apFactorPS_eq_of_lt` (Pentagonal)
is the only analytic input; everything below is the AP-product *algebra* that, together with the
two Jacobi-triple-product product-forms (isolated as `JTP_*` below), reduces `P0`/`P12` to the
common mod-18 AP product.  Numerically verified (`/tmp/zwnum.py`). -/

open scoped PowerSeries.WithPiTopology
open QseriesFormalization.Pending.JTPFormalPSPentagonal (qPochAPPS apFactorPS
     )

/-! ### Negative AP products `apKneg r m = (−Q^r;Q^m)_∞` and the sign-pairing

We mirror `apK` with the `(1 + X^{r+mn})` factors.  Multipliability is the same `order → ∞`
argument (sign-independent).  The single nontrivial fact is the **sign-pairing**
`(Q^k;Q^m)_∞ · (−Q^k;Q^m)_∞ = (Q^{2k};Q^{2m})_∞`, i.e. `apK k m · apKneg k m = apK (2k) (2m)`,
which is the factorwise `(1−X^j)(1+X^j) = 1−X^{2j}` lifted through `HasProd.mul`. -/

/-! ### The two product identities `P0`/`P12` (JTP + mod-18 AP splitting)

Both `(P0)` and `(P12)` reduce, by the Jacobi triple product and the AP-product pairing
`(q;q³)(−q;q³)=(q²;q⁶)` etc., to the *same* mod-18 arithmetic-progression product.  See the design
doc §"The two product identities".  Numerically verified (`/tmp/zwnum.py`) to high order. -/

/-! #### Bridges to the HM Laurent layer (`jLaurent`, `qPochAPLaurent`)

`K = HahnSeries ℤ ℚ = QLaurent` definitionally, so the HM objects live in `K`.  We bridge the
alternating thetas `JQ15`, `JQ9` to `jLaurent` (HM's coefficient-defined alternating theta), and
`apK` is literally `qPochAPLaurent`. -/

open QseriesFormalization.Pending.Ch10HM

theorem QseriesFormalization.Ch10TwoVar.JK_eq_jLaurent (a b : ℤ) (ha : 0 < a) (hab : a < b) (hb : 0 < b) :
    JK b a hb (fun r => (-1) ^ r) = jLaurent a b := by sorry
