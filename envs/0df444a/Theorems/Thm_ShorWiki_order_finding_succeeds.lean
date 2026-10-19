-- Prove2me | Theorems.Thm_ShorWiki_order_finding_succeeds
-- name    : ShorWiki.order_finding_succeeds
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T03:09:01.202691+00:00
-- url     : https://prove2.me/theorems/1368ff99-a0f1-4a39-9b0b-9deadb88df92
-- title:
--   Shor's order-finding subroutine: each $j/r$ is observed with probability $\ge 4/(\pi^2 r)$ and recovered by continued fractions
-- statement:
--   Let $1 < a < N$ be integers with $\gcd(a,N) = 1$, let $r = \operatorname{ord}_N(a)$ be the order of $a$ modulo $N$, let $n = \lceil \log_2 N\rceil$, and let $Q = 2^{2n}$. Run Shor's order-finding circuit — quantum phase estimation for the modular-multiplication gate $U|k\rangle = |ak \bmod N\rangle$ with a $2n$-qubit first register — on the input $|0\rangle^{\otimes 2n}\otimes|1\rangle$, and measure the first register, obtaining an outcome $k \in \{0, \dots, Q-1\}$ with probability $P(k)$.
--
--   Fix $j \in \{0, 1, \dots, r-1\}$ and call an outcome $k$ *optimal for $j$* if
--   $$\left|\frac{k}{2^{2n}} - \frac{j}{r}\right| \le \frac{1}{2^{2n+1}},$$
--   i.e. $k$ is a nearest integer to $2^{2n} j / r$. The theorem states:
--
--   1. the optimal outcomes for $j$ are observed with total probability
--   $$\sum_{k \text{ optimal for } j} P(k) \;\ge\; \frac{4}{\pi^2\, r};$$
--   2. for every outcome $k$ optimal for $j$, some convergent of the continued fraction expansion of $k/2^{2n}$ equals $\dfrac{j/\gcd(j,r)}{r/\gcd(j,r)}$ in lowest terms.
--
--   Summing (1) over the $r$ values of $j$, a single run of the subroutine yields, with probability at least $4/\pi^2 \approx 0.405$, an outcome from which the continued fractions algorithm recovers the reduced fraction $j/r$ for some $j$ — and hence the divisor $r/\gcd(j,r)$ of the order $r$. This is the precise content of the article's claim that phase estimation "gives as output a random integer of the form $\frac{j}{r}2^{2n}$" and that $2n$ qubits suffice for the continued fractions algorithm to recover it.
--
--   **Formalization Note** The probability $P(k)$ is computed from the explicit circuit defined in `ShorWiki_Defs` (Hadamard gates, the controlled gates $C\text{-}U^{2^i}$, inverse QFT). The convergents are Mathlib's `Real.convergent` of the real number $k/2^{2n}$, and "recovers $j/\gcd(j,r)$ and $r/\gcd(j,r)$" is expressed as equality of the numerator and denominator of that rational convergent. The value $4/(\pi^2 r)$ combines the article's two statements "balanced probability $1/r$ to find each $|\phi_j\rangle$" and "$p_{2^{2n}j/r} \ge 4/\pi^2$".
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, sections "Quantum order-finding subroutine", "Quantum phase estimation", "Continued-fraction algorithm to retrieve the period" and "Choosing the size of the first register" (PDF pp. 3–6)

import Mathlib
import Definitions.Def_ShorWiki_Defs

open Matrix Kronecker

namespace ShorWiki

theorem order_finding_succeeds (N a : ℕ) (ha : 1 < a) (haN : a < N)
    (hcop : Nat.Coprime a N) (j : ℕ) (hj : j < ord N a) :
    4 / (Real.pi ^ 2 * ord N a) ≤
        (∑ k ∈ Finset.univ.filter (fun k : Fin (2 ^ (2 * regBits N)) =>
            |((k : ℕ) : ℝ) / 2 ^ (2 * regBits N) - (j : ℝ) / ord N a|
              ≤ 1 / 2 ^ (2 * regBits N + 1)),
          measureFirst (orderFindingOutput N a) k) ∧
      ∀ k : Fin (2 ^ (2 * regBits N)),
        |((k : ℕ) : ℝ) / 2 ^ (2 * regBits N) - (j : ℝ) / ord N a|
            ≤ 1 / 2 ^ (2 * regBits N + 1) →
          ∃ m : ℕ,
            (Real.convergent (((k : ℕ) : ℝ) / 2 ^ (2 * regBits N)) m).num
                = ((j / Nat.gcd j (ord N a) : ℕ) : ℤ) ∧
            (Real.convergent (((k : ℕ) : ℝ) / 2 ^ (2 * regBits N)) m).den
                = ord N a / Nat.gcd j (ord N a) := by sorry

end ShorWiki
