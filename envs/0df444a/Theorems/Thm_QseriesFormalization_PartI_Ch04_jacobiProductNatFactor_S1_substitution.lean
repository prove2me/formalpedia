-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04_jacobiProductNatFactor_S1_substitution
-- name    : QseriesFormalization.PartI.Ch04.jacobiProductNatFactor_S1_substitution
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:30:35.547431+00:00
-- url     : https://prove2.me/theorems/b4ac74f5-b8fc-42ac-a72a-7d386d687f9c
-- title:
--   Jacobi product factor at $(Y^5,-Y)$ is a mod-5 triple of factors
-- statement:
--   Let $q,Y\in\mathbb{C}$ with $Y\ne0$, $Y^2=q$, and $n\in\mathbb{N}$. The $n$-th factor of the Jacobi triple product at parameters $(Y^5,-Y)$, namely $(1-Y^{10(n+1)})(1-Y^{10n+6})(1-Y^{10n+4})$, equals
--   $$(1-q^{5+5n})(1-q^{3+5n})(1-q^{2+5n}),$$
--   i.e. the product of the mod-5 residue factors `rrMod5Factor q k n` for $k=5,3,2$. This is a termwise identity used in Chapter 4 to obtain the product side of a Rogers-Ramanujan-type theta identity.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04.lean#L548-L581

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

theorem QseriesFormalization.PartI.Ch04.jacobiProductNatFactor_S1_substitution
    (q Y : ℂ) (hYne : Y ≠ 0) (hYq : Y ^ 2 = q) (n : ℕ) :
    Ch02.jacobiProductNatFactor (Y ^ 5) (-Y) n =
      rrMod5Factor q 5 n * rrMod5Factor q 3 n * rrMod5Factor q 2 n := by sorry
