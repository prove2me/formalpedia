-- Prove2me | Theorems.Thm_ShorWiki_mulModGate_pow_ord
-- name    : ShorWiki.mulModGate_pow_ord
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T03:00:46.889034+00:00
-- url     : https://prove2.me/theorems/8a1fad29-fa0b-4e2b-99c4-88f052f62d3e
-- title:
--   The modular-multiplication gate satisfies $U^r = I$
-- statement:
--   Let $1 < a < N$ with $\gcd(a,N)=1$, let $r = \operatorname{ord}_N(a)$ and $n = \lceil\log_2 N\rceil$. The $n$-qubit gate
--   $$U|k\rangle = \begin{cases} |ak \bmod N\rangle & 0 \le k < N,\\ |k\rangle & N \le k < 2^n\end{cases}$$
--   satisfies
--   $$U^r = I .$$
--
--   This periodicity of the gate is what quantum phase estimation exploits: it determines the spectrum of $U$.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Quantum phase estimation" (PDF p. 4)

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem mulModGate_pow_ord (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) :
    mulModGate N a (regBits N) ^ ord N a = 1 := by sorry

end ShorWiki
