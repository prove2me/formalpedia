-- Prove2me | Theorems.Thm_ShorWiki_gcd_pow_half_nontrivial
-- name    : ShorWiki.gcd_pow_half_nontrivial
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T03:00:05.088988+00:00
-- url     : https://prove2.me/theorems/e20ecf58-1ede-4005-9928-d2b966c7c533
-- title:
--   Classical reduction: $\gcd(N, a^{r/2} \mp 1)$ are nontrivial factors when $N \nmid a^{r/2}+1$
-- statement:
--   Let $1 < a < N$ with $\gcd(a, N) = 1$ and let $r = \operatorname{ord}_N(a)$. Suppose $r$ is even and $N \nmid a^{r/2} + 1$. Then both
--   $$d = \gcd\!\left(N,\ a^{r/2} - 1\right) \quad\text{and}\quad d' = \gcd\!\left(N,\ a^{r/2} + 1\right)$$
--   are nontrivial factors of $N$:
--   $$1 < d < N, \qquad 1 < d' < N .$$
--
--   This is the success criterion of Shor's algorithm: an even order with $a^{r/2} \not\equiv -1 \pmod N$ splits $N$ by a single gcd computation.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Classical reduction" (PDF p. 3) and restated algorithm, step 6

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem gcd_pow_half_nontrivial (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (heven : Even (ord N a))
    (hndvd : ¬ N ∣ a ^ (ord N a / 2) + 1) :
    (1 < Nat.gcd N (a ^ (ord N a / 2) - 1) ∧ Nat.gcd N (a ^ (ord N a / 2) - 1) < N) ∧
      (1 < Nat.gcd N (a ^ (ord N a / 2) + 1) ∧ Nat.gcd N (a ^ (ord N a / 2) + 1) < N) := by sorry

end ShorWiki
