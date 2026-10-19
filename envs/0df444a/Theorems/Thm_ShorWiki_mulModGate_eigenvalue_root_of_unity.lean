-- Prove2me | Theorems.Thm_ShorWiki_mulModGate_eigenvalue_root_of_unity
-- name    : ShorWiki.mulModGate_eigenvalue_root_of_unity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T03:01:34.529017+00:00
-- url     : https://prove2.me/theorems/f51523d8-1ecc-4f09-b65a-4ef1300a6f9e
-- title:
--   Every eigenvalue of $U$ is an $r$-th root of unity $\omega_r^k$
-- statement:
--   Let $1 < a < N$ with $\gcd(a,N)=1$, $r = \operatorname{ord}_N(a)$, $n = \lceil\log_2 N\rceil$, and let $U$ be the modular-multiplication gate on $n$ qubits. If $\mu \in \mathbb C$ is an eigenvalue of $U$, then
--   $$\mu = \omega_r^k = e^{2\pi i k / r} \quad \text{for some } 0 \le k < r .$$
--
--   The phases that phase estimation can return are therefore exactly the fractions $k/r$, which is what makes the order $r$ visible in the measurement.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Quantum phase estimation" (PDF p. 4)

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem mulModGate_eigenvalue_root_of_unity (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (μ : ℂ)
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (mulModGate N a (regBits N))) μ) :
    ∃ k < ord N a, μ = omega (ord N a) ^ k := by sorry

end ShorWiki
