-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04_jacobiInfiniteProduct_S2_eq_mod5_triple
-- name    : QseriesFormalization.PartI.Ch04.jacobiInfiniteProduct_S2_eq_mod5_triple
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:29:46.830305+00:00
-- url     : https://prove2.me/theorems/710acb7f-9fac-43cc-9497-4e03058eee69
-- title:
--   Jacobi infinite product at $(Y^5,-Y^3)$ equals three mod-5 products
-- statement:
--   Let $q,Y\in\mathbb{C}$ with $Y\ne0$, $Y^2=q$ and $|q|<1$. The Jacobi infinite product at $(Y^5,-Y^3)$ equals
--   $$\prod_{n\ge0}(1-q^{5n+5})\cdot\prod_{n\ge0}(1-q^{5n+4})\cdot\prod_{n\ge0}(1-q^{5n+1}),$$
--   that is, $(q^5;q^5)_\infty(q^4;q^5)_\infty(q;q^5)_\infty$. This is the product side of the second mod-5 theta identity in Chapter 4.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04.lean#L671-L691

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
open QseriesFormalization.PartI.Ch04

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

theorem QseriesFormalization.PartI.Ch04.jacobiInfiniteProduct_S2_eq_mod5_triple
    (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) (hq : ‖q‖ < 1) :
    Ch02.jacobiInfiniteProduct (Y ^ 5) (-Y ^ 3) =
      (∏' n : ℕ, rrMod5Factor q 5 n) * (∏' n : ℕ, rrMod5Factor q 4 n) *
      (∏' n : ℕ, rrMod5Factor q 1 n) := by sorry
