-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04_eulerPentagonalInfiniteProduct_eq_tsum
-- name    : QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct_eq_tsum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:28:15.780105+00:00
-- url     : https://prove2.me/theorems/cd2ec077-f970-42a9-981e-a8adcb87d3aa
-- title:
--   Euler's pentagonal number theorem (analytic form, $q\ne0$)
-- statement:
--   For $q\in\mathbb{C}$ with $0<|q|<1$,
--   $$\prod_{n\ge1}(1-q^{n})=\sum_{j\in\mathbb{Z}}(-1)^jq^{j(3j+1)/2}.$$
--   This is Euler's pentagonal number theorem (Theorem 4.2 of the book) for complex $q$ in the open unit disc, obtained from the Jacobi triple product; the exponent $j(3j+1)/2$ is an integer for every $j\in\mathbb{Z}$ and is read as a Lean integer power.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04.lean#L1028-L1034

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

theorem QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct_eq_tsum
    (q : ℂ) (hqnorm : ‖q‖ < 1) (hq : q ≠ 0) :
    eulerPentagonalInfiniteProduct q =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (3 * j + 1) / 2) := by sorry
