-- Prove2me | Theorems.Thm_ShorWiki_mulModGate_mulVec_eigState
-- name    : ShorWiki.mulModGate_mulVec_eigState
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T03:02:53.734258+00:00
-- url     : https://prove2.me/theorems/54bc5aaf-1c10-4c59-ab26-37ab6f52eba3
-- title:
--   $|\psi_j\rangle$ is an eigenvector of $U$ with eigenvalue $\omega_r^j$
-- statement:
--   Let $1 < a < N$ with $\gcd(a,N)=1$, $r = \operatorname{ord}_N(a)$, $n = \lceil\log_2 N\rceil$, and let $U$ be the modular-multiplication gate. For every integer $j \ge 0$ the state
--   $$|\psi_j\rangle = \frac{1}{\sqrt r}\sum_{k=0}^{r-1} \omega_r^{-kj}\,|a^k \bmod N\rangle$$
--   is nonzero and satisfies
--   $$U|\psi_j\rangle = \omega_r^{j}\,|\psi_j\rangle .$$
--
--   These are the eigenstates to which phase estimation is applied; the eigenvalue $\omega_r^j = e^{2\pi i j/r}$ carries the phase $j/r$.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Quantum phase estimation" (PDF p. 4)

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem mulModGate_mulVec_eigState (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (j : ℕ) :
    eigState N a (regBits N) j ≠ 0 ∧
      mulModGate N a (regBits N) *ᵥ eigState N a (regBits N) j
        = omega (ord N a) ^ j • eigState N a (regBits N) j := by sorry

end ShorWiki
