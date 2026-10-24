-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04_qpoch_q4_residue_split
-- name    : QseriesFormalization.PartI.Ch04.qpoch_q4_residue_split
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:31:45.78362+00:00
-- url     : https://prove2.me/theorems/cc488948-77b5-4615-8d7e-baa6baef310f
-- title:
--   Splitting $(q^4;q^4)_\infty$ by residues of $m$ modulo 3
-- statement:
--   For $q\in\mathbb{C}$ with $|q|<1$,
--   $$\prod_{m\ge0}(1-q^{12m+4})\prod_{m\ge0}(1-q^{12m+8})\prod_{m\ge0}(1-q^{12m+12})=\prod_{m\ge0}(1-q^{4m+4}).$$
--   That is, the infinite product $(q^4;q^4)_\infty$ is the product of its three subproducts over exponents congruent to $4,8,12$ modulo $12$. This is used in the evaluation of the quintuple product kernel in Chapter 4.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04.lean#L4269-L4351

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

theorem QseriesFormalization.PartI.Ch04.qpoch_q4_residue_split (q : ℂ) (hqnorm : ‖q‖ < 1) :
    (∏' m : ℕ, ((1 : ℂ) - q ^ (12 * m + 4))) *
        (∏' m : ℕ, ((1 : ℂ) - q ^ (12 * m + 8))) *
        (∏' m : ℕ, ((1 : ℂ) - q ^ (12 * m + 12))) =
      ∏' m : ℕ, ((1 : ℂ) - q ^ (4 * m + 4)) := by sorry
