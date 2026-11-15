-- Prove2me | Theorems.Thm_QuantumLTF_Membership_centered_product_expand
-- name    : QuantumLTF.Membership.centered_product_expand
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-14T21:34:44.212632+00:00
-- url     : https://prove2.me/theorems/7b9a52f9-2801-42db-8cc7-68cb3bc4d6bd
-- title:
--   Expansion of a centered Fourier product
-- statement:
--   For a nonzero complex grid size $N$, expanding the product of the shifted coordinates gives
--   $$N(j/N+c)(k/N+c)=jk/N+cj+ck+Nc^2.$$
--   In the centered-grid Fourier transform, the first term is the ordinary QFT phase, the next two terms are the row and column phase corrections, and the final term is a shared constant phase.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Lemma 3.3, p. 27 (PDF p. 28), Eqs. (44)–(48), algebraic expansion used between Eqs. (47) and (48).

import Mathlib

namespace QuantumLTF.Membership

/-- The scalar expansion underlying the centered-grid Fourier phase. -/
theorem centered_product_expand (N j k c : ℂ) (hN : N ≠ 0) :
    N * (j / N + c) * (k / N + c) =
      j * k / N + c * j + c * k + N * c ^ 2 := by sorry

end QuantumLTF.Membership
