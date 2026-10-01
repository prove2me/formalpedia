-- Prove2me | Theorems.Thm_ShorAlgorithms_OrderFinding_order_recovered_prob_ge
-- name    : ShorAlgorithms.OrderFinding.order_recovered_prob_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T09:41:24.998302+00:00
-- url     : https://prove2.me/theorems/699bec31-38a5-45ee-b6c4-31b00a8fc9ad
-- title:
--   Quantum order finding recovers the order $r$ with probability at least $\varphi(r)/3r$
-- statement:
--   There is a threshold $N$ such that the following holds for every $n \ge N$. Let $x$ be coprime to $n$ and let $r$ be its multiplicative order modulo $n$, the least $r \ge 1$ with $x^r \equiv 1 \pmod n$. Let $q = 2^l$ be the power of $2$ with $n^2 \le q < 2n^2$. Run Shor's order-finding procedure: prepare the state
--
--   $$
--   \frac{1}{q^{1/2}}\sum_{a=0}^{q-1}|a\rangle|x^a \bmod n\rangle,
--   $$
--
--   apply the Fourier transform $A_q$ to the first register, measure, and round $c/q$ to the nearest fraction with denominator smaller than $n$. Then the probability that the observed $c$ gives us $r$ (the rounded fraction has denominator $r$ in lowest terms) is at least
--
--   $$
--   \frac{\varphi(r)}{3r}.
--   $$
--
--   This is the paper's main claim about the quantum part of the factoring algorithm; combined with $\varphi(r)/r > \delta/\log\log r$, it shows that $O(\log\log r)$ repetitions find $r$ with high probability.
--
--   **Formalization Note** The probability of the event is $\sum_{c \text{ good}} \sum_{y \in \mathbb{Z}/n} |\Psi(c, y)|^2$, where $\Psi$ is built by applying $A_q$ to the first register of (5.2); summing over all $y$ is exact, since values $y$ that are not powers of $x$ have probability $0$. "Gives us $r$" is `yieldsOrder`. The threshold $N$ comes first and is uniform in $x$ and $q$; it is inherited from the paper's per-state bound, which holds "for sufficiently large $n$". `[NeZero n]` makes $\mathbb{Z}/n$ finite.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1501, §5, "Since each of these states occurs with probability at least 1/3r^2, we obtain r with probability at least φ(r)/3r"; setup pp. 1498–1500

import Mathlib
import Definitions.Def_ShorAlgorithms_OrderFinding_outcomeProb
import Definitions.Def_ShorAlgorithms_OrderFinding_yieldsOrder

namespace ShorAlgorithms.OrderFinding

open Classical in
/-- Shor (1997), §5, p. 1501 (goal). For all sufficiently large `n` (threshold `N` uniform in
`x` and `q`): let `x` be coprime to `n` with order `r`, and `q = 2^l` with `n² ≤ q < 2n²`.
Run the order-finding algorithm (state (5.2), Fourier transform `A_q` on the first register,
measurement). The probability that the observed `c` gives us `r` by rounding `c/q` to the
nearest fraction with denominator smaller than `n` is at least `φ(r)/(3r)`. -/
theorem order_recovered_prob_ge : ∃ N : ℕ, ∀ (n : ℕ) [NeZero n], N ≤ n →
    ∀ x : ℕ, Nat.Coprime x n → ∀ q l : ℕ, q = 2 ^ l → n ^ 2 ≤ q → q < 2 * n ^ 2 →
    (Nat.totient (orderOf (x : ZMod n)) : ℝ) / (3 * (orderOf (x : ZMod n) : ℝ)) ≤
      ∑ c ∈ (Finset.univ : Finset (Fin q)).filter
          (fun c : Fin q => yieldsOrder n q (orderOf (x : ZMod n)) (c : ℕ)),
        ∑ y : ZMod n, outcomeProb n x q c y := by sorry

end ShorAlgorithms.OrderFinding
