-- Prove2me | Theorems.Thm_SemialgebraicSDP_Psatz_gram_psd_isSumSq
-- name    : SemialgebraicSDP.Psatz.gram_psd_isSumSq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:15:26.213731+00:00
-- url     : https://prove2.me/theorems/3a9e1f63-e8c5-4a35-a939-63a18b773cf1
-- title:
--   §3.2 — a positive semidefinite Gram matrix gives a sum of squares
-- statement:
--   Let $n,d\in\mathbb N$, let $z$ be the vector of monomials of total degree at most $d$ in $n$ variables, and let $Q$ be a real symmetric positive semidefinite matrix indexed by these monomials. Then the polynomial
--   $$
--   F=z^TQz
--   $$
--   is a sum of squares in $\mathbb R[x_1,\dots,x_n]$: there are polynomials $p_1,\dots,p_r$ with $F=\sum_i p_i^2$.
--
--   This is the sufficiency half of the Gram matrix method: any positive semidefinite point of the affine space of Gram matrices of $F$ certifies that $F$ is a sum of squares and hence nonnegative.
--
--   **Formalization Note** "Sum of squares" is Mathlib's `IsSumSq` in the polynomial ring (finite sums of squares; the empty sum $0$ included).
-- source:
--   Parrilo, Semidefinite programming relaxations for semialgebraic problems, Math. Program. Ser. B 96 (2003) 293–320, p. 298, §3.2, last paragraph

import Mathlib
import Definitions.Def_SemialgebraicSDP_Psatz_Gram

namespace SemialgebraicSDP.Psatz

open MvPolynomial

theorem gram_psd_isSumSq {n d : ℕ} (Q : Matrix (Mon n d) (Mon n d) ℝ)
    (hQ : Q.PosSemidef) : IsSumSq (gramPoly Q) := by sorry

end SemialgebraicSDP.Psatz
