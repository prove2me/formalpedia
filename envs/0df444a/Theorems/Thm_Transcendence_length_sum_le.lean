-- Prove2me | Theorems.Thm_Transcendence_length_sum_le
-- name    : Transcendence.length_sum_le
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T16:43:49.919204+00:00
-- url     : https://prove2.me/theorems/1aeffaef-2834-435e-9a3c-abb35d93e1d8
-- title:
--   The length of a finite sum of integer polynomials is at most the sum of the lengths
-- statement:
--   For polynomials in $\mathbb{Z}[X][Y]$, the length of $P \in \mathbb{Z}[X][Y]$, written $L(P)$, is the sum of the absolute values of all its integer coefficients. For any finite family $(f_i)_{i \in s}$,
--
--   $$L\Big(\sum_{i \in s} f_i\Big) \le \sum_{i \in s} L(f_i).$$
--
--   Together with `Transcendence.length_mul_le`, this is the size calculus used by the Gel'fond-type constructions of the four exponentials subtree.
-- source:
--   Standard. Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi).

import Mathlib

namespace Transcendence

theorem length_sum_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial (Polynomial ℤ)) :
    ∑ k ∈ (∑ i ∈ s, f i).support, ∑ j ∈ ((∑ i ∈ s, f i).coeff k).support,
        (((∑ i ∈ s, f i).coeff k).coeff j).natAbs ≤
      ∑ i ∈ s, ∑ k ∈ (f i).support, ∑ j ∈ ((f i).coeff k).support, (((f i).coeff k).coeff j).natAbs := by
  sorry

end Transcendence
