-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch02_summable_jacobiInfiniteSeries_terms
-- name    : QseriesFormalization.PartI.Ch02.summable_jacobiInfiniteSeries_terms
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:20:15.134652+00:00
-- url     : https://prove2.me/theorems/6e0113d3-ce9e-4314-9e32-7652324a124e
-- title:
--   Summability of the bilateral Jacobi series $\sum_{n\in\mathbb{Z}}z^nq^{n^2}$
-- statement:
--   For complex numbers $q,z$ with $|q|<1$, the family $n\mapsto z^nq^{n^2}$ indexed by $n\in\mathbb{Z}$ is summable, using Lean’s totalized integer powers. In particular, $0^{-1}=0$ and $0$ raised to a negative integer is $0$. When $z\ne0$, this is convergence of the usual bilateral Jacobi series $$\sum_{n\in\mathbb{Z}}z^nq^{n^2}.$$ The Lean summability statement also includes $z=0$ under the stated convention. This is an analytic preliminary in Chapter 2.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 2. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter02.lean#L277-L290

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

theorem QseriesFormalization.PartI.Ch02.summable_jacobiInfiniteSeries_terms (q z : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℤ => z ^ n * q ^ (n ^ 2) := by sorry
