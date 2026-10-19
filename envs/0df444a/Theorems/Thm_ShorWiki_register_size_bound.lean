-- Prove2me | Theorems.Thm_ShorWiki_register_size_bound
-- name    : ShorWiki.register_size_bound
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T03:07:59.88175+00:00
-- url     : https://prove2.me/theorems/2348d404-e6c2-4daa-ad33-a29a93176e36
-- title:
--   Register size: $\frac{1}{2^{2n+1}} \le \frac{1}{2N^2} \le \frac{1}{2r^2}$
-- statement:
--   Let $1 < a < N$ with $\gcd(a,N)=1$, $r = \operatorname{ord}_N(a)$ and $n = \lceil\log_2 N\rceil$. Then
--   $$\frac{1}{2^{2n+1}} \;\le\; \frac{1}{2N^2} \;\le\; \frac{1}{2r^2}.$$
--
--   This is why a first register of $2n$ qubits suffices: an optimal outcome $k$ approximates $j/r$ to within $1/2^{2n+1}$, which is within the range of the continued fraction theorem.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Choosing the size of the first register" (PDF p. 6)

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem register_size_bound (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) :
    (1 : ℝ) / 2 ^ (2 * regBits N + 1) ≤ 1 / (2 * (N : ℝ) ^ 2) ∧
      1 / (2 * (N : ℝ) ^ 2) ≤ 1 / (2 * (ord N a : ℝ) ^ 2) := by sorry

end ShorWiki
