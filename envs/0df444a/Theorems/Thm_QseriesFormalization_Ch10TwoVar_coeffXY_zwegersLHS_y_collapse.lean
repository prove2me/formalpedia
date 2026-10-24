-- Prove2me | Theorems.Thm_QseriesFormalization_Ch10TwoVar_coeffXY_zwegersLHS_y_collapse
-- name    : QseriesFormalization.Ch10TwoVar.coeffXY_zwegersLHS_y_collapse
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T08:57:50.828229+00:00
-- url     : https://prove2.me/theorems/b88e2b08-db15-46dd-8f64-d7801b4fa746
-- title:
--   Circle-sum collapse of the $y^l$-slice of the Zwegers lattice sum
-- statement:
--   Let $L$ be the analogous sum with $y^l$ in place of $x^l$ (`zwegersLHS_y`). For integers $l,a$, the coefficient of $Q^a$ in the $y^l$-slice of $L$ equals the finite sum $\sum_{k\in\mathbb{Z}:\ k^2+l^2=a}(-1)^{k+l}(\delta(k)-\delta(l))$ (a sum over lattice points on a circle). Chapter 10.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 10. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter10_TwoVar.lean#L3598-L3634

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

namespace QseriesFormalization.Pending.Ch10HM end QseriesFormalization.Pending.Ch10HM

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

/-! #### RHS product forms and AP refinements (free from the HM Laurent layer)

The alternating thetas `JQ15`/`JQ9` factor by the (positive) Jacobi triple product
`jLaurent_eq_tripleProductInf`, and the pochhammers `poch_q = apK 3 3`, `poch_q2 = apK 6 6`
refine into mod-18 APs by `qPochAPLaurent_refine_mul`.  These are the RHS-side ingredients
of `P0`/`P12`; all are transported verbatim from the committed HM layer. -/

open QseriesFormalization.Pending.Ch10HM

/-! #### Mod-18 refinements of the level-9 AP products (for the `P12` clearing). -/

/-! ### The two negative Jacobi triple product *product forms* (genuine analytic input)

These are the sole remaining analytic facts: the bilateral all-`+1`-weight theta
`J(−z;q) = ∑_r z^r q^{T r}` equals the Jacobi-triple-product
`(q;q)_∞ (−z;q)_∞ (−q/z;q)_∞`, instantiated at `(z,q) = (1,Q⁹)` and `(Q⁶,Q⁹)`:

  `Jneg1  = 2·(−Q⁹;Q⁹)_∞²·(Q⁹;Q⁹)_∞ = 2·apKneg 9 9·apKneg 9 9·apK 9 9`,
  `JnegQ6 = (−Q³;Q⁹)_∞·(−Q⁶;Q⁹)_∞·(Q⁹;Q⁹)_∞ = apKneg 3 9·apKneg 6 9·apK 9 9`.

(The factor `2` for `Jneg1` is the `z=1` degeneracy: the `r ↦ 1−r` symmetry of the
exponent `9·T(r)` doubles the constant term.)  Both are the negative-`z`
(`z ↦ −Qpow a`) instance of HM's `jLaurent_eq_tripleProductInf` chain; numerically
verified to `Q^400`. -/

open QseriesFormalization.Pending.Ch10HM

/-! #### The negative-`z` Jacobi triple product chain (`0 < a < b`)

We mirror HM's positive chain (`jLaurent_eq_tripleProductInf`) but instantiate Chan's finite
JTP at `z = −Qpow a`.  Then `(−z)^l = (Qpow a)^l = Qpow(a·l)`, so the alternating `(-1)^l`
weight disappears and the RHS becomes the **all-`+1`** theta `∑_r Q^{b·T(r)+a·r}`.  The product
factors `(z;q)_N (z⁻¹q;q)_N` become the `apKneg` partials `(−Q^a;Q^b)_N (−Q^{b-a};Q^b)_N`.
All product-side / Gaussian-binomial / window machinery is sign-independent and reused verbatim
from HM; only the term-weight changes from `negOnePowIntQ` to `1`. -/

/-! ##### Bridge: my `Qpow`/`.coeff` are defeq to HM's `Qpow`/`lcoeff`. -/

/-! ##### The negative triple-product partial and its coefficient (heart of the chain). -/

/-! ##### Product side: the partial product as a formal power series and its stabilization. -/

/-! ##### The degenerate `A = 0` case (for `Jneg1`, `z = 1`).

The general theorem needs `0 < A` only through the window/degree bounds
`abs_le_jExp_of_pos_lt` and `degree_sub_lt_center_start` (the Gaussian collapse and product side
are `A`-independent).  For `A = 0` those *exact* bounds fail at `n = 1` (`jExp 0 B 1 = 0`), but the
weaker facts they are used for still hold.  We reprove just those two facts for `A = 0`, then mirror
the heart / extensionality with `A = 0`. -/

/-! ##### `A = 0` heart and extensionality. -/

/-! ### `P0`/`P12` reduced to the two `apKneg`-cleared negative-JTP identities

All the AP-product *algebra* below is now fully proved (RHS triple products `JQ15_prod`/`JQ9_prod`,
the mod-18 refinements `apK_*_refine`, the sign-pairing `apK_mul_apKneg`, the nonzero lemmas
`apK_ne_zero`, and the domain structure of `K = HahnSeries ℤ ℚ`).  Multiplying `P0` through by the
nonzero factor `apK 9 18` and `P12` through by `apK 3 18·apK 15 18`, and cancelling, reduces each to
a single **cleared negative Jacobi-triple-product identity** (numerically verified, `verify6.py`):

  `Jneg1 · apK 9 18                = single 0 2 · apK 18 18`,
  `JnegQ6 · apK 3 18 · apK 15 18   = apK 9 18 · apK 18 18`.

These two are the genuine remaining analytic input — the bilateral all-`+1`-weight theta sum
`J(−z;q) = ∑_r z^r q^{T r}` equals an arithmetic-progression product.  They are the negative-`z`
(`z ↦ −Qpow a`) instance of HM's `jLaurent_eq_tripleProductInf` chain (finite JTP `z = −Qpow a` →
coefficient stabilization → infinite `(±Q^·;Q^·)_∞` product), isolated here as the sole `sorry`. -/

/-! ### `y`-version (by the same argument with `x ↔ y`). -/

/-! The `y`-version analytic inputs (mirror of the `x`-version under `x ↔ y`). -/

/-! ### `y`-mirror slice reductions (identical to the `x`-side with the slots swapped). -/

theorem QseriesFormalization.Ch10TwoVar.coeffXY_zwegersLHS_y_collapse (l a : ℤ) :
    (coeffXY zwegersLHS_y 0 l).coeff a
      = ∑ᶠ k : ℤ, (if k ^ 2 + l ^ 2 = a then zW k l else 0) := by sorry
