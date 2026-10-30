-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch02_summable_jacobiSeries_nat
-- name    : QseriesFormalization.PartI.Ch02.summable_jacobiSeries_nat
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:20:16.787967+00:00
-- url     : https://prove2.me/theorems/711fe292-e815-4181-a23b-b92fc14def31
-- title:
--   Summability of the one-sided Jacobi series $\sum_{n\ge0}z^nq^{n^2}$
-- statement:
--   For complex numbers $q,z$ with $|q|<1$, the series $\sum_{n\ge0}z^{n}q^{n^{2}}$ is summable. The quadratic exponent makes the terms eventually bounded by a geometric series, for every fixed $z$.
--
--   This is an analytic preliminary in Chapter 2 for the Jacobi triple product identity, ensuring that the series side makes sense.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 2. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter02.lean#L244-L275

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib

/-!
# Chapter 2 — Part I: First proof of Jacobi's triple product (functional equation)

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 2, pp. 5–10.)

Chapter 2 proves Jacobi's triple product identity by exhibiting a function
that satisfies a functional equation `F(qz) = (1 + z) F(z)` and pinning it
down via growth/uniqueness arguments.

Truncated forms of the product and bilateral series are defined here as
recursive `def`s; the infinite forms `jacobiInfiniteProduct` and
`jacobiInfiniteSeries` use Mathlib's `tprod` and `tsum`. The final identity
`jacobiTripleProduct` is proved in `Chapter03.lean`, where the finite-JTP
machinery needed for the Gaussian-tail argument is available.
-/

variable {R : Type*} [Field R]

open Filter
open scoped Topology

theorem QseriesFormalization.PartI.Ch02.summable_jacobiSeries_nat (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => z ^ n * q ^ (n * n) := by sorry
