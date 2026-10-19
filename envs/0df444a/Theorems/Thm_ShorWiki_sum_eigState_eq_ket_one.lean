-- Prove2me | Theorems.Thm_ShorWiki_sum_eigState_eq_ket_one
-- name    : ShorWiki.sum_eigState_eq_ket_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T03:04:10.097647+00:00
-- url     : https://prove2.me/theorems/d19fd67e-4b47-41c4-942a-af82d2c81d81
-- title:
--   $\frac{1}{\sqrt r}\sum_{j=0}^{r-1}|\psi_j\rangle = |1\rangle$
-- statement:
--   Let $1 < a < N$ with $\gcd(a,N)=1$, $r = \operatorname{ord}_N(a)$ and $n = \lceil\log_2 N\rceil$. The eigenstates $|\psi_j\rangle$ of the modular-multiplication gate satisfy
--   $$\frac{1}{\sqrt r}\sum_{j=0}^{r-1} |\psi_j\rangle = |1\rangle$$
--   in the $n$-qubit register.
--
--   So the easily prepared input $|1\rangle$ is an equal-weight superposition of all eigenstates, and phase estimation on $|1\rangle$ samples a uniformly random $j$.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Quantum phase estimation" (PDF pp. 4–5)

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem sum_eigState_eq_ket_one (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) :
    (1 / Real.sqrt (ord N a) : ℂ) • ∑ j ∈ Finset.range (ord N a), eigState N a (regBits N) j
      = ket (2 ^ regBits N) 1 := by sorry

end ShorWiki
