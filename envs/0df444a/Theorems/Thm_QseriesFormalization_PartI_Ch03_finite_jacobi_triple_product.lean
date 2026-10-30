-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch03_finite_jacobi_triple_product
-- name    : QseriesFormalization.PartI.Ch03.finite_jacobi_triple_product
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:21:12.718979+00:00
-- url     : https://prove2.me/theorems/59002a8f-d0c5-4e3f-a057-8a47b7e02141
-- title:
--   The finite Jacobi triple product (Theorem 3.3)
-- statement:
--   Let $R$ be a field, $q,z\in R$ nonzero and $n\in\mathbb{N}$. Then
--   $$(z;q)_n\,(z^{-1}q;q)_n=\sum_{k=0}^{2n}\binom{2n}{k}_q\,q^{(k-n)(k-n-1)/2}\,(-z)^{k-n},$$
--   where $(a;q)_n=\prod_{k=0}^{n-1}(1-aq^k)$ is the $q$-Pochhammer symbol and $\binom{2n}{k}_q$ is the Gaussian binomial coefficient. This is the finite form of Jacobi's triple product identity from Chapter 3; letting $n\to\infty$ gives the infinite identity.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 3. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter03.lean#L1297-L1312

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

theorem QseriesFormalization.PartI.Ch03.finite_jacobi_triple_product (q z : R) (hz : z ≠ 0) (hq : q ≠ 0) (n : Nat) :
    qPoch z q n * qPoch (z⁻¹ * q) q n = finiteJTPRHS q z n := by sorry
