-- Prove2me | Theorems.Thm_ShorWiki_measureFirst_orderFindingOutput
-- name    : ShorWiki.measureFirst_orderFindingOutput
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T03:04:57.60913+00:00
-- url     : https://prove2.me/theorems/c119e11c-fa9c-4df0-920e-b2fcc84c6a23
-- title:
--   Measuring the first register: each $|\phi_j\rangle$ appears with probability $1/r$
-- statement:
--   Let $1 < a < N$ with $\gcd(a,N)=1$, $r = \operatorname{ord}_N(a)$ and $n = \lceil\log_2 N\rceil$. Let $P(k)$ be the probability of outcome $k$ when the first register of the order-finding output state (phase estimation applied to $|0\rangle^{\otimes 2n}|1\rangle$) is measured, and let $P_j(k)$ be the corresponding probability for the output of phase estimation applied to $|0\rangle^{\otimes 2n}|\psi_j\rangle$. Then for every $k$,
--   $$P(k) = \frac{1}{r}\sum_{j=0}^{r-1} P_j(k).$$
--
--   So the measurement on the actual input $|1\rangle$ behaves as if a uniformly random $j \in \{0,\dots,r-1\}$ had been chosen first and phase estimation then run on $|\psi_j\rangle$.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, section "Quantum phase estimation" (PDF p. 5)

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem measureFirst_orderFindingOutput (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (k : Fin (2 ^ (2 * regBits N))) :
    measureFirst (orderFindingOutput N a) k
      = (1 / (ord N a : ℝ)) * ∑ j ∈ Finset.range (ord N a),
          measureFirst (phaseEstimationCircuit N a (regBits N) (2 * regBits N) *ᵥ
            tensorState (ket (2 ^ (2 * regBits N)) 0) (eigState N a (regBits N) j)) k := by sorry

end ShorWiki
