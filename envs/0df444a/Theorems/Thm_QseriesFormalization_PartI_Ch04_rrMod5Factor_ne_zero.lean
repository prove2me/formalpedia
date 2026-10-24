-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04_rrMod5Factor_ne_zero
-- name    : QseriesFormalization.PartI.Ch04.rrMod5Factor_ne_zero
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:32:55.602801+00:00
-- url     : https://prove2.me/theorems/434021f3-8d04-4ec8-9778-cfc1e1c89952
-- title:
--   The factors $1-q^{k+5n}$ are nonzero for $|q|<1$
-- statement:
--   For $q\in\mathbb{C}$ with $|q|<1$, natural numbers $k\ge1$ and $n$, the factor $1-q^{k+5n}$ (the $n$-th factor of $(q^k;q^5)_\infty$) is nonzero. The reason is that $|q^{k+5n}|<1$. This is a technical fact used when dividing products in Chapter 4's derivation of the Rogers-Ramanujan-type mod 5 products from the Jacobi triple product.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04.lean#L437-L450

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

theorem QseriesFormalization.PartI.Ch04.rrMod5Factor_ne_zero (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    rrMod5Factor q k n ≠ 0 := by sorry
