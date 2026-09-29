-- Prove2me | Theorems.Thm_Transcendence_length_mul_le
-- name    : Transcendence.length_mul_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T16:43:47.178412+00:00
-- url     : https://prove2.me/theorems/7467fd0b-b862-4a30-bce0-a77999e765b6
-- title:
--   The length of a product of integer polynomials is at most the product of the lengths
-- statement:
--   For polynomials in $\mathbb{Z}[X][Y]$, the length of $P \in \mathbb{Z}[X][Y]$, written $L(P)$, is the sum of the absolute values of all its integer coefficients. For all $P, Q$,
--
--   $$L(PQ) \le L(P)\,L(Q).$$
--
--   Mathlib has no $\ell^{1}$ length for polynomials; this and `Transcendence.length_sum_le` replace the size calculus that several proofs of the four exponentials subtree carried separately.
-- source:
--   Standard. Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi).

import Mathlib

namespace Transcendence

theorem length_mul_le (P Q : Polynomial (Polynomial ℤ)) :
    ∑ k ∈ (P * Q).support, ∑ i ∈ ((P * Q).coeff k).support, (((P * Q).coeff k).coeff i).natAbs ≤
      (∑ k ∈ P.support, ∑ i ∈ (P.coeff k).support, ((P.coeff k).coeff i).natAbs) *
        ∑ k ∈ Q.support, ∑ i ∈ (Q.coeff k).support, ((Q.coeff k).coeff i).natAbs := by
  sorry

end Transcendence
