-- Prove2me | Theorems.Thm_RamanujanPetersson_tau_multiplicative
-- name    : RamanujanPetersson.tau_multiplicative
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:13:11.828972+00:00
-- url     : https://prove2.me/theorems/aeace769-463e-46a0-bf4e-916f8d2013ab
-- title:
--   Multiplicativity of $\tau$ (Mordell 1917)
-- statement:
--   Ramanujan's tau function is multiplicative: $\tau(1)=1$, and for all natural numbers $m,n$ with $\gcd(m,n)=1$,
--
--   $$\tau(mn)=\tau(m)\,\tau(n).$$
--
--   This is the first of Ramanujan's 1916 conjectures, proved by Mordell in 1917. It is what makes the Euler product of $L(s,\tau)$ possible.
--
--   **Formalization Note** $\tau$ is `RamanujanPetersson.tau`, the $n$-th coefficient of Mathlib's $q$-expansion (period $1$) of `ModularForm.discriminant`, valued in $\mathbb C$.
-- source:
--   Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), section "Ramanujan conjecture", Ramanujan's conjecture 1 ("$\tau$ is multiplicative"); proved by Mordell (1917) per the following paragraph

import Mathlib
import Definitions.Def_RamanujanPetersson_tau

open UpperHalfPlane Filter Asymptotics MatrixGroups
open scoped Real

namespace RamanujanPetersson

theorem tau_multiplicative :
    tau 1 = 1 ∧ ∀ m n : ℕ, m.Coprime n → tau (m * n) = tau m * tau n := by sorry

end RamanujanPetersson
