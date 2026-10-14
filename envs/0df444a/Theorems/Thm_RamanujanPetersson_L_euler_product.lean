-- Prove2me | Theorems.Thm_RamanujanPetersson_L_euler_product
-- name    : RamanujanPetersson.L_euler_product
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T16:20:18.305808+00:00
-- url     : https://prove2.me/theorems/05e7e8e6-265a-41a4-8961-f91493e799e4
-- title:
--   Euler product of $L(s,\tau)$
-- statement:
--   For every complex $s$ with $\operatorname{Re}s>13/2$, the Ramanujan $L$-series $L(s,\tau)=\sum_{n\ge1}\tau(n)n^{-s}$ has the two Euler product expansions
--
--   $$L(s,\tau)=\prod_{p\ \text{prime}}\ \sum_{n=0}^{\infty}\frac{\tau(p^n)}{p^{ns}}=\prod_{p\ \text{prime}}\frac{1}{1-\tau(p)p^{-s}+p^{11-2s}},$$
--
--   with both infinite products over all primes converging unconditionally to $L(s,\tau)$.
--
--   The first form comes from multiplicativity, and the second from the prime-power recursion.
--
--   **Formalization Note** $\tau$ is `RamanujanPetersson.tau`, the $n$-th coefficient of Mathlib's $q$-expansion (period $1$) of `ModularForm.discriminant`, valued in $\mathbb C$. The products are Mathlib's `HasProd` over `Nat.Primes`.
-- source:
--   Wikipedia, "Ramanujan–Petersson conjecture", https://en.wikipedia.org/w/index.php?title=Ramanujan%E2%80%93Petersson_conjecture&oldid=1369029052 (PDF snapshot supplied by the proposer, 9 pp.), section "Ramanujan L-function", the two displayed Euler products ("the L-series in the domain of convergence can be written as the following Euler product" and the simplified form $\prod_p 1/(1-\tau(p)p^{-s}+p^{11-2s})$)

import Mathlib
import Definitions.Def_RamanujanPetersson_tau

open UpperHalfPlane Filter Asymptotics MatrixGroups
open scoped Real

namespace RamanujanPetersson

theorem L_euler_product (s : ℂ) (hs : 13 / 2 < s.re) :
    HasProd (fun p : Nat.Primes =>
        ∑' n : ℕ, tau ((p : ℕ) ^ n) / ((p : ℕ) : ℂ) ^ ((n : ℂ) * s)) (LSeries tau s) ∧
    HasProd (fun p : Nat.Primes =>
        (1 - tau p * ((p : ℕ) : ℂ) ^ (-s) + ((p : ℕ) : ℂ) ^ (11 - 2 * s))⁻¹) (LSeries tau s) := by sorry

end RamanujanPetersson
