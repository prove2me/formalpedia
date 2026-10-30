-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch03_gaussianBinom_mul_qPochhammer_eq
-- name    : QseriesFormalization.PartI.Ch03.gaussianBinom_mul_qPochhammer_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:21:23.647449+00:00
-- url     : https://prove2.me/theorems/46ec46d9-3f2f-40f6-a62f-0a434540994a
-- title:
--   Product form of the Gaussian binomial coefficient: $\binom{n}{m}_q (q;q)_m(q;q)_{n-m}=(q;q)_n$
-- statement:
--   Let $R$ be a commutative ring and $q\in R$. For all natural numbers $m\le n$,
--   $$\binom{n}{m}_q\,(q;q)_m\,(q;q)_{n-m}=(q;q)_n,$$
--   where $\binom{n}{m}_q$ is the Gaussian (q-binomial) coefficient, defined by the Pascal-type recursion $\binom{n+1}{k+1}_q=\binom{n}{k+1}_q+q^{n-k}\binom{n}{k}_q$, and $(q;q)_n=\prod_{j=1}^{n}(1-q^j)$. This is the usual closed form of the q-binomial coefficient, stated without division, and is a basic fact from Chapter 3.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 3. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter03.lean#L340-L397

import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Chapter 3 — Part I: Second proof (Gaussian polynomials and the q-binomial theorem)

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 3, pp. 11–20.)

Gaussian (q-binomial) coefficients are defined in `Basic.lean`. This file
states and proves the finite q-binomial theorem
`∏_{k=0}^{n-1} (1 + x q^k) = ∑_{k=0}^n [n choose k]_q q^{k(k-1)/2} x^k`.

The main theorem is proved by induction from the defining q-Pascal recursion
for Gaussian binomial coefficients.
-/

open QseriesFormalization

variable {R : Type*} [CommRing R]

variable {R : Type*} [CommSemiring R]

variable {R : Type*} [CommRing R]

theorem QseriesFormalization.PartI.Ch03.gaussianBinom_mul_qPochhammer_eq (q : R) :
    ∀ n m, m ≤ n →
      gaussianBinom q n m * qPochhammer q m * qPochhammer q (n - m) =
        qPochhammer q n
  := by sorry
