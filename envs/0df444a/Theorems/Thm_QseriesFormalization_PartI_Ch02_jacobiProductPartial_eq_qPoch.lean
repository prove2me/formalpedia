-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch02_jacobiProductPartial_eq_qPoch
-- name    : QseriesFormalization.PartI.Ch02.jacobiProductPartial_eq_qPoch
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:19:45.620872+00:00
-- url     : https://prove2.me/theorems/58f23c69-09a7-4806-8d02-73b0f00eaf8e
-- title:
--   The finite Jacobi triple product equals three $q$-Pochhammer symbols
-- statement:
--   For complex numbers $q,z$ and a natural number $N$, let $\mathrm{jacobiProductPartial}(q,z,N)=\prod_{n=0}^{N-1}(\text{even factor}_n)(\text{odd factor}_n(z))(\text{odd factor}_n(z^{-1}))$ be the finite truncation of the Jacobi triple product. The statement says
--   $$\prod_{n=0}^{N-1}\!\big(1-q^{2n+2}\big)\big(1+zq^{2n+1}\big)\big(1+z^{-1}q^{2n+1}\big)=(q^2;q^2)_N\,(-zq;q^2)_N\,(-z^{-1}q;q^2)_N,$$
--   where $(a;p)_N=\prod_{k=0}^{N-1}(1-ap^k)$ is the $q$-Pochhammer symbol. The even factor is $1-q^{2(n+1)}$ and the odd factors are $1+c\,q^{2(n+1)-1}$ with $c=z$ and $c=z^{-1}$.
--
--   This rewrites the product side of the Jacobi triple product (Chapter 2) in $q$-Pochhammer form.
--
--   Integer powers and reciprocals use Lean’s totalized convention: $0^{-1}=0$, so $0$ raised to a negative integer is $0$. The usual reciprocal interpretation applies when the base is nonzero.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 2. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter02.lean#L126-L159

import Definitions.Def_QseriesFormalization_DefCoreQSeries
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

open QseriesFormalization
open QseriesFormalization.PartI
open QseriesFormalization.PartI.Ch02

variable {R : Type*} [Field R]

open Filter
open scoped Topology

theorem QseriesFormalization.PartI.Ch02.jacobiProductPartial_eq_qPoch (q z : ℂ) (N : ℕ) :
    jacobiProductPartial q z N =
      qPoch (q ^ 2) (q ^ 2) N * qPoch (-(z * q)) (q ^ 2) N *
        qPoch (-(z⁻¹ * q)) (q ^ 2) N := by sorry
