-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04_eulerPentagonalInfiniteProduct_eq_tsum_prime
-- name    : QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct_eq_tsum_prime
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:28:45.424475+00:00
-- url     : https://prove2.me/theorems/caa7a84c-ff55-46ba-a7ef-a7f12e580e1d
-- title:
--   Euler's pentagonal number theorem for all $|q|<1$
-- statement:
--   For every complex $q$ with $|q|<1$ (including $q=0$),
--   $$\prod_{n\ge1}(1-q^{n})=\sum_{j\in\mathbb{Z}}(-1)^jq^{j(3j+1)/2}.$$
--   This is Euler's pentagonal number theorem (Theorem 4.2), the version without the hypothesis $q\ne0$ (the case $q=0$ being a direct check).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04.lean#L1036-L1076

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

theorem QseriesFormalization.PartI.Ch04.eulerPentagonalInfiniteProduct_eq_tsum_prime (q : ℂ) (hqnorm : ‖q‖ < 1) :
    eulerPentagonalInfiniteProduct q =
      ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (3 * j + 1) / 2) := by sorry
