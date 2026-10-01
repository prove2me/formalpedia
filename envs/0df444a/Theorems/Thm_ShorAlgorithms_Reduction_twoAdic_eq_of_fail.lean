-- Prove2me | Theorems.Thm_ShorAlgorithms_Reduction_twoAdic_eq_of_fail
-- name    : ShorAlgorithms.Reduction.twoAdic_eq_of_fail
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T08:36:56.294484+00:00
-- url     : https://prove2.me/theorems/3a33217d-48db-4fbe-a50e-2adb519f60e3
-- title:
--   §5, p. 1498 — the reduction fails only if the 2-parts of all the local orders r_i agree
-- statement:
--   Let $n > 1$ be odd with prime factorization $n = \prod_{i=1}^k p_i^{\alpha_i}$, let $x$ be a unit modulo $n$ and let $r_i$ be the order of $x \bmod p_i^{\alpha_i}$. Write $\nu_2(m)$ for the exponent of the largest power of $2$ dividing $m$. If the procedure does not yield a nontrivial factor of $n$ at $x$ — that is, $r$ is odd or $\gcd(x^{r/2}-1, n) \in \{1, n\}$ — then
--
--   $$
--   \nu_2(r_1) = \nu_2(r_2) = \cdots = \nu_2(r_k).
--   $$
--
--   Contrapositively, whenever two of the local orders have different 2-adic valuations, $x$ is a good choice. Combined with the estimate that the valuations all agree for at most a $1/2^{k-1}$ fraction of units, this gives the mission's goal.
--
--   **Formalization Note** Only the direction "failure implies agreement" is stated, which is the direction the page's "The algorithm only fails if all of these powers of 2 agree" asserts and the goal needs; the converse (also true for odd $n$) is the page's description of the two agreeing cases and is not part of this statement. Oddness of $n$ is needed: modulo a power of $2$, $-1$ and $1$ can coincide.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1498, §5, "Consider the largest power of 2 dividing each r_i. The algorithm only fails if all of these powers of 2 agree"

import Mathlib
import Definitions.Def_ShorAlgorithms_Reduction_successEvent
import Definitions.Def_ShorAlgorithms_Reduction_localOrder

namespace ShorAlgorithms.Reduction

/-- Shor (1997), §5, p. 1498: the algorithm only fails if the largest powers of 2 dividing the
local orders `r_i` all agree. For odd `n > 1` and a unit `x` for which the procedure does not
yield a nontrivial factor, the 2-adic valuations of `r_p` coincide for all prime factors `p`. -/
theorem twoAdic_eq_of_fail (n : ℕ) (hodd : Odd n) (hn : 1 < n) (u : (ZMod n)ˣ)
    (hfail : ¬ successEvent n u) :
    ∀ p ∈ n.primeFactors, ∀ q ∈ n.primeFactors,
      padicValNat 2 (localOrder n u p) = padicValNat 2 (localOrder n u q) := by sorry

end ShorAlgorithms.Reduction
