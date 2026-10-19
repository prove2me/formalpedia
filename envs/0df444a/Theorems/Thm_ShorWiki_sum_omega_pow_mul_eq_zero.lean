-- Prove2me | Theorems.Thm_ShorWiki_sum_omega_pow_mul_eq_zero
-- name    : ShorWiki.sum_omega_pow_mul_eq_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T03:03:25.546139+00:00
-- url     : https://prove2.me/theorems/94849d8f-ed6b-4de3-98b7-2f44a998e0a4
-- title:
--   Geometric series: $\sum_{j=0}^{r-1}\omega_r^{jk} = 0$ for $1 \le k \le r-1$
-- statement:
--   Let $r$ be a positive integer, $\omega_r = e^{2\pi i/r}$, and $1 \le k \le r-1$. Then
--   $$\sum_{j=0}^{r-1} \omega_r^{jk} = 0 .$$
--
--   This is the cancellation used to show that the uniform superposition of the eigenstates $|\psi_j\rangle$ collapses to the single basis state $|1\rangle$.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Quantum phase estimation" (PDF p. 5)

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem sum_omega_pow_mul_eq_zero (r k : ℕ) (hk : 1 ≤ k) (hkr : k ≤ r - 1) :
    ∑ j ∈ Finset.range r, omega r ^ (j * k) = 0 := by sorry

end ShorWiki
