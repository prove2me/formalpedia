-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch03_summand_shift
-- name    : QseriesFormalization.PartI.Ch03.summand_shift
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:22:57.827284+00:00
-- url     : https://prove2.me/theorems/7603ff9a-dafe-4848-9e5a-9a130e801939
-- title:
--   Summand of the finite Jacobi triple product as a shifted $q$-binomial term
-- statement:
--   Let $R$ be a field, $q,z\in R$ nonzero, and $n,k\in\mathbb{N}$. Let $S_{n,k}$ be the $k$-th summand ($0\le k\le 2n$) of the finite Jacobi triple product sum, namely $S_{n,k}=\binom{2n}{k}_q\,q^{l(l-1)/2}(-z)^l$ with $l=k-n$. Then
--   $$(-z)^n S_{n,k}=\binom{2n}{k}_q\,q^{k(k-1)/2}(-1)^k\Big(\frac{z}{q^n}\Big)^k q^{n(n+1)/2}.$$
--   That is, up to the factor $q^{n(n+1)/2}$, each summand is the $q$-binomial theorem term at $z/q^n$. This identity is used in Chapter 3 to derive the finite Jacobi triple product from the $q$-binomial theorem.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 3. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter03.lean#L1190-L1239

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
open QseriesFormalization.PartI
open QseriesFormalization.PartI.Ch03

variable {R : Type*} [CommRing R]

variable {R : Type*} [CommSemiring R]

variable {R : Type*} [CommRing R]

open Filter
open scoped Topology

open Filter
open scoped Topology

variable {R : Type*} [Field R]

/-! ### Summand and sum identities for the finite Jacobi triple product -/

theorem QseriesFormalization.PartI.Ch03.summand_shift (q z : R) (hz : z ≠ 0) (hq : q ≠ 0) (n k : Nat) :
    (-z) ^ n * finiteJTPSummand q z n k =
      gaussianBinom q (2 * n) k * q ^ (k * (k - 1) / 2) * (-1) ^ k *
        (z / q ^ n) ^ k * q ^ (triangular n) := by sorry
