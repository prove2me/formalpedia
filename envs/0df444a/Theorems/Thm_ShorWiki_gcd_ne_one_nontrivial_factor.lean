-- Prove2me | Theorems.Thm_ShorWiki_gcd_ne_one_nontrivial_factor
-- name    : ShorWiki.gcd_ne_one_nontrivial_factor
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T02:58:22.545064+00:00
-- url     : https://prove2.me/theorems/88779db7-21d0-44ab-a12c-5f55e13ccdc2
-- title:
--   Classical reduction: if $\gcd(a,N) \ne 1$ then it is a nontrivial factor of $N$
-- statement:
--   Let $1 < a < N$ be integers and let $K = \gcd(a, N)$. If $K \ne 1$, then $K$ is a nontrivial factor of $N$:
--   $$K \mid N, \qquad 1 < K < N .$$
--
--   This is step 3 of the article's restated algorithm: before any quantum computation, a lucky choice of $a$ sharing a factor with $N$ already splits $N$ as $K \cdot (N/K)$.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Classical reduction", restated algorithm, steps 1–3 (PDF p. 3)

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem gcd_ne_one_nontrivial_factor (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hK : Nat.gcd a N ≠ 1) :
    Nat.gcd a N ∣ N ∧ 1 < Nat.gcd a N ∧ Nat.gcd a N < N := by sorry

end ShorWiki
