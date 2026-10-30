-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04_quintuple_double_sum_shear
-- name    : QseriesFormalization.PartI.Ch04.quintuple_double_sum_shear
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:32:24.585794+00:00
-- url     : https://prove2.me/theorems/edc40390-2c33-4a0e-b284-27da78874c89
-- title:
--   Product of two theta series as a sheared double sum (quintuple product)
-- statement:
--   For complex $q,z$ with $|q|<1$, $q\ne0$, $z\ne0$,
--   $$\Big(\sum_{r\in\mathbb{Z}}(-z)^rq^{r^2}\Big)\Big(\sum_{s\in\mathbb{Z}}\Big(-\frac{z^2}{q^2}\Big)^{s}q^{2s^2}\Big)=\sum_{k\in\mathbb{Z}}(-1)^kz^kq^{k^2}\sum_{s\in\mathbb{Z}}(-1)^sq^{6s^2-(4k+2)s}.$$
--   This is the change of summation variables (a shear of the double sum) that turns a product of two Jacobi theta series into an iterated sum; it is one step in the proof of the quintuple product identity in Chapter 4.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04.lean#L4159-L4241

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Chapter 4 — Part I: Some applications of Jacobi's triple product

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 4, pp. 21–30.)

This chapter spins off four named identities from the Jacobi triple
product (Theorem 4.1, Euler's pentagonal theorem, Theorem 4.3, the
quintuple product identity).  The Jacobi triple product is now available;
the remaining infinite applications need the specialization and rewriting
layers connecting those products and bilateral sums to Chan's displayed forms.
-/

open QseriesFormalization
open QseriesFormalization.PartI

open QseriesFormalization.PartI.Ch02 (jacobiInfiniteProduct jacobiInfiniteSeries)
open QseriesFormalization.PartI.Ch03 (finiteJTPRHS)
open Filter

open scoped Topology

variable {R : Type*} [Field R]

/- The infinite Theorem 4.1 equality is now reduced to specializing JTP and
rewriting the resulting product and bilateral series into Chan's displayed form. -/

/-! ## Mod-5 residue factors for Rogers-Ramanujan (Ch7 dependency)

The classical R-R proof needs:
`(q;q)_∞ = ∏_{k=1..5} (q^k;q^5)_∞`.

Each factor `(q^k;q^5)_∞` = `∏'_n (1 - q^(k + 5n))` for `n ≥ 0`. -/

/-! ### Rogers-Ramanujan theta series via JTP at q^5

S₁(q) := ∑'_{j : ℤ} (-1)^j · q^(j(5j+1)/2) — JTP series at Q := Y^5, z := -Y (Y² = q).
S₂(q) := ∑'_{j : ℤ} (-1)^j · q^(j(5j+3)/2) — JTP series at Q := Y^5, z := -Y^3 (Y² = q).
-/

/- The infinite Euler pentagonal theorem is proved above as
`eulerPentagonalInfiniteProduct_eq_tsum`. -/

/- The infinite Theorem 4.3 identity is deferred until its JTP specialization
and rewriting layer is formalized. -/

/- The infinite quintuple product identity is deferred to the JTP specialization
and rewriting layer used in Chan's proof. -/

/-! ### Finite JTP specialized at z = 1: Euler pentagonal general identity -/

/-! ### Quintuple product identity: final assembly via Tannery-style convergence

The strategy: prove both the LHS product truncation and the qPoch⁶×combinedMonomialSum
converge to `quintupleProductLHS`, then their difference → 0, closing the identity.

Key bridge: a generic "fixed-core + uniform-tail" convergence lemma. -/

open scoped Topology
open Filter

/-! ### Quintuple product: uniform tail estimate for the combined monomial sum -/

/-! Dead Route B end-cap removed: the bridge to `quintupleProductRHS` is now
done entirely via Route A (JTP product decomposition) below. The upstream
`qPoch_qsix_mul_quintupleCombinedMonomial*` and `tendsto_qPoch_mul_quintupleFiniteJTPCombinedMonomial*`
infrastructure is retained in case it's useful for future routes. -/

/-! #### Route A: Product decomposition via JTP

The quintuple product factors decompose as:
  quintupleProductFactor(n) = JacobiNatFactor(q, -z, n) × JacobiNatFactor(q², -z²/q², n) / (1-q^{4n+4})

At the infinite product level:
  quintupleProductLHS = jacobiInfiniteProduct(q, -z) × jacobiInfiniteProduct(q², -z²/q²) / (q⁴;q⁴)_∞

Then JTP converts each infinite product to a bilateral series, and the product
of two series (after mod-3 regrouping) gives ExplicitRHS. -/

theorem QseriesFormalization.PartI.Ch04.quintuple_double_sum_shear
    (q z : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) (hz : z ≠ 0) :
    (∑' r : ℤ, (-z) ^ r * q ^ (r ^ 2)) *
      (∑' s : ℤ, (-(z ^ 2 / q ^ 2)) ^ s * (q ^ 2) ^ (s ^ 2)) =
      ∑' k : ℤ, (-1 : ℂ) ^ k * z ^ k * q ^ (k ^ 2) *
        (∑' s : ℤ, (-1 : ℂ) ^ s * q ^ (6 * s ^ 2 - (4 * k + 2) * s)) := by sorry
