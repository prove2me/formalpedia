-- Prove2me | Theorems.Thm_RamanujanPetersson_tau_prime_power_recursion
-- name    : RamanujanPetersson.tau_prime_power_recursion
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:14:03.460444+00:00
-- url     : https://prove2.me/theorems/d96f83e5-142a-461f-aabc-8f1db08c16d2
-- title:
--   Prime-power recursion for $\tau$ (Mordell 1917)
-- statement:
--   Ramanujan's tau function is **not** completely multiplicative, i.e. there exist natural numbers $m,n$ with $\tau(mn)\neq\tau(m)\tau(n)$. Moreover, for every prime $p$ and every integer $j\ge 2$,
--
--   $$\tau(p^{j+1})=\tau(p)\,\tau(p^j)-p^{11}\,\tau(p^{j-1}).$$
--
--   This is the second of Ramanujan's 1916 conjectures, proved by Mordell in 1917. It is what makes each Euler factor of $L(s,\tau)$ the reciprocal of a quadratic polynomial in $p^{-s}$.
--
--   **Formalization Note** $\tau$ is `RamanujanPetersson.tau`, the $n$-th coefficient of Mathlib's $q$-expansion (period $1$) of `ModularForm.discriminant`, valued in $\mathbb C$. The range $j\ge2$ is copied from the source. The classical recursion also holds for $j=1$, but that case is not part of this statement.
-- source:
--   Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), section "Ramanujan conjecture", Ramanujan's conjecture 2 ("$\tau$ is not completely multiplicative, but has the following recursive dependence for prime $p$ and $j\ge2$"); proved by Mordell (1917)

import Mathlib
import Definitions.Def_RamanujanPetersson_tau

open UpperHalfPlane Filter Asymptotics MatrixGroups
open scoped Real

namespace RamanujanPetersson

theorem tau_prime_power_recursion :
    (∃ m n : ℕ, tau (m * n) ≠ tau m * tau n) ∧
    ∀ p : ℕ, p.Prime → ∀ j : ℕ, 2 ≤ j →
      tau (p ^ (j + 1)) = tau p * tau (p ^ j) - (p : ℂ) ^ 11 * tau (p ^ (j - 1)) := by sorry

end RamanujanPetersson
