-- Prove2me | Theorems.Thm_ShorWiki_dvd_pow_half_sub_one_mul_add_one
-- name    : ShorWiki.dvd_pow_half_sub_one_mul_add_one
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T02:59:04.794771+00:00
-- url     : https://prove2.me/theorems/d4c89de7-04d3-43e6-af8d-95a64b594c08
-- title:
--   Classical reduction: $N \mid (a^{r/2}-1)(a^{r/2}+1)$ when the order $r$ is even
-- statement:
--   Let $1 < a < N$ with $\gcd(a, N) = 1$, and let $r = \operatorname{ord}_N(a)$ be the order of $a$ modulo $N$. If $r$ is even, then
--   $$N \mid \left(a^{r/2} - 1\right)\left(a^{r/2} + 1\right).$$
--
--   This is the difference-of-squares factorisation of $a^r - 1$, on which the classical reduction of factoring to order finding rests.
--
--   **Formalization Note** The statement is in natural numbers; since $a \ge 2$, $a^{r/2} - 1$ involves no truncated subtraction.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Classical reduction" (PDF p. 3)

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem dvd_pow_half_sub_one_mul_add_one (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (heven : Even (ord N a)) :
    N ∣ (a ^ (ord N a / 2) - 1) * (a ^ (ord N a / 2) + 1) := by sorry

end ShorWiki
