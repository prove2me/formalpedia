-- Prove2me | Theorems.Thm_ShorAlgorithms_Reduction_factor_prob_ge
-- name    : ShorAlgorithms.Reduction.factor_prob_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T08:51:40.446044+00:00
-- url     : https://prove2.me/theorems/10d88a2b-4f48-4e69-b9c6-bbb60b855ba6
-- title:
--   Shor's reduction: a random unit x mod odd n yields a nontrivial factor with probability ≥ 1 − 1/2^{k−1}
-- statement:
--   Let $n > 1$ be an odd integer with $k$ distinct (necessarily odd) prime factors, and let $\varphi(n)$ be the number of units modulo $n$. Choose $x$ uniformly at random from $(\mathbb{Z}/n\mathbb{Z})^\times$, let $r$ be its multiplicative order, and compute $\gcd(x^{r/2} - 1, n)$. The procedure **yields a nontrivial factor of $n$** when $r$ is even and $1 < \gcd(x^{r/2}-1, n) < n$. Then
--
--   $$
--   \Pr_{x}\bigl[\text{the procedure yields a nontrivial factor of } n\bigr] \;\ge\; 1 - \frac{1}{2^{k-1}},
--   $$
--
--   that is, $\bigl(1 - 2^{-(k-1)}\bigr)\,\varphi(n) \le \#\{x \in (\mathbb{Z}/n)^\times : \text{success at } x\}$.
--
--   This is the classical half of Shor's factoring algorithm: it reduces factoring an odd $n$ to finding the order of a random element. The bound is informative exactly when $n$ is not a prime power ($k \ge 2$), where it is at least $1/2$; for a prime power ($k = 1$) it reads $0$ and holds trivially. The paper's remark that "the scheme will work as long as $n$ is odd and not a prime power" explains when the bound is useful and is not an extra hypothesis. The constant is sharp: for $n = 21$ exactly $6$ of the $12$ units succeed.
--
--   **Formalization Note** The sample space is the unit group `(ZMod n)ˣ`, of cardinality $\varphi(n)$; a non-unit $x$ has no multiplicative order and is not sampled (Shor's "choose a random $x \pmod n$" in "the multiplicative group $\pmod n$"). The probability is stated in cleared-denominator form over $\mathbb{R}$, with the count taken as `Nat.card` of the subtype of successful units. `n.primeFactors.card` is $k$, which is at least $1$ for $n > 1$, so `k - 1` does not truncate. The success event is the definition `successEvent`.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1498, §5, "Using this criterion, it can be shown that this procedure, when applied to a random x (mod n), yields a nontrivial factor of n with probability at least 1 − 1/2^{k−1}, where k is the number of distinct odd prime factors of n."

import Mathlib
import Definitions.Def_ShorAlgorithms_Reduction_successEvent

namespace ShorAlgorithms.Reduction

/-- Shor (1997), §5, p. 1498: for odd `n > 1` with `k` distinct (odd) prime factors, the
procedure applied to a uniformly random unit `x (mod n)` yields a nontrivial factor of `n`
with probability at least `1 - 1/2^{k-1}`; stated as
`(1 - 1/2^{k-1}) · φ(n) ≤ #{x ∈ (ℤ/n)ˣ : success}`. -/
theorem factor_prob_ge (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    (1 - 1 / 2 ^ (n.primeFactors.card - 1) : ℝ) * (Nat.totient n : ℝ)
      ≤ (Nat.card {u : (ZMod n)ˣ // successEvent n u} : ℝ) := by sorry

end ShorAlgorithms.Reduction
