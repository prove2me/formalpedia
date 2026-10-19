-- Prove2me | Theorems.Thm_ShorWiki_not_dvd_pow_half_sub_one
-- name    : ShorWiki.not_dvd_pow_half_sub_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T02:59:38.110284+00:00
-- url     : https://prove2.me/theorems/e23ac1f1-0879-420f-b5bf-d58517bc19bf
-- title:
--   Classical reduction: $N \nmid a^{r/2} - 1$ when the order $r$ is even
-- statement:
--   Let $1 < a < N$ with $\gcd(a, N) = 1$ and let $r = \operatorname{ord}_N(a)$. If $r$ is even, then
--   $$N \nmid a^{r/2} - 1 .$$
--
--   Otherwise $a^{r/2} \equiv 1 \pmod N$, contradicting the minimality of the order $r$. Together with the previous milestone this shows that the only way the reduction can fail for even $r$ is $N \mid a^{r/2}+1$.
--
--   **Formalization Note** Natural-number subtraction is harmless here because $a^{r/2} \ge 1$.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Classical reduction" (PDF p. 3)

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem not_dvd_pow_half_sub_one (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (heven : Even (ord N a)) :
    ¬ N ∣ a ^ (ord N a / 2) - 1 := by sorry

end ShorWiki
