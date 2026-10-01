-- Prove2me | Theorems.Thm_ShorAlgorithms_OrderFinding_outcome_prob_eq
-- name    : ShorAlgorithms.OrderFinding.outcome_prob_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T09:15:19.070913+00:00
-- url     : https://prove2.me/theorems/76d57f61-9321-4882-8a94-73c0e67ee2a6
-- title:
--   §5, eqs. (5.5)–(5.6) — probability of observing $|c, x^k \bmod n\rangle$
-- statement:
--   Let $n \ge 1$, let $x$ be coprime to $n$ with multiplicative order $r$ modulo $n$, and let $q = 2^l$ be the power of $2$ with $n^2 \le q < 2n^2$. Let $0 \le c < q$ and $0 \le k < r$. The probability that measuring the final state (5.4) of the order-finding algorithm gives $|c, x^k \bmod n\rangle$ equals both
--
--   $$
--   \left|\frac{1}{q}\sum_{\substack{0\le a<q\\ x^a\equiv x^k}}\exp(2\pi i a c/q)\right|^2
--   \quad\text{and}\quad
--   \left|\frac{1}{q}\sum_{b=0}^{\lfloor(q-k-1)/r\rfloor}\exp\bigl(2\pi i(br+k)c/q\bigr)\right|^2 .
--   $$
--
--   The first expression collects the paths $|a\rangle \mapsto |c\rangle$ that end in the same second-register value; the second rewrites the index set $\{a : a \equiv k \pmod r\}$ as $a = br + k$. The second form is the starting point of the estimate (5.11).
--
--   **Formalization Note** The probability is `outcomeProb`, the squared modulus of the amplitude of the state built by applying $A_q$ to (5.2). $\lfloor (q-k-1)/r \rfloor$ is natural-number division, and the natural-number subtraction $q - k - 1$ is exact because $k < r < n \le q$ (the order of a unit is at most $\varphi(n) < n$). The hypotheses on $q$ are the section's standing choice of $q$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1499, §5, eqs. (5.5)–(5.6); choice of q p. 1498

import Mathlib
import Definitions.Def_ShorAlgorithms_OrderFinding_outcomeProb

namespace ShorAlgorithms.OrderFinding

/-- Shor (1997), §5, eqs. (5.5)–(5.6), p. 1499. Let `r` be the order of `x` mod `n`, let
`q = 2^l` with `n² ≤ q < 2n²`, and let `0 ≤ k < r`. The probability of observing
`|c, x^k (mod n)⟩` in the final state (5.4) equals
(5.5) `|(1/q) ∑_{a < q, x^a ≡ x^k} exp(2πiac/q)|²`, and also equals
(5.6) `|(1/q) ∑_{b=0}^{⌊(q-k-1)/r⌋} exp(2πi(br+k)c/q)|²`.
`(q - k - 1) / r` is natural-number (floor) division; `k < r < n ≤ q` keeps the subtraction
exact. -/
theorem outcome_prob_eq (n x q l : ℕ) (hx : Nat.Coprime x n)
    (hq : q = 2 ^ l) (hnq : n ^ 2 ≤ q) (hq2 : q < 2 * n ^ 2)
    (c : Fin q) (k : ℕ) (hk : k < orderOf (x : ZMod n)) :
    outcomeProb n x q c ((x : ZMod n) ^ k) =
        ‖(1 / (q : ℂ)) * ∑ a ∈ (Finset.univ : Finset (Fin q)).filter
            (fun a : Fin q => (x : ZMod n) ^ (a : ℕ) = (x : ZMod n) ^ k),
          Complex.exp (2 * Real.pi * Complex.I * ((a : ℕ) : ℂ) * ((c : ℕ) : ℂ) / (q : ℂ))‖ ^ 2 ∧
    outcomeProb n x q c ((x : ZMod n) ^ k) =
        ‖(1 / (q : ℂ)) * ∑ b ∈ Finset.range ((q - k - 1) / orderOf (x : ZMod n) + 1),
          Complex.exp (2 * Real.pi * Complex.I *
            (((b * orderOf (x : ZMod n) + k : ℕ)) : ℂ) * ((c : ℕ) : ℂ) / (q : ℂ))‖ ^ 2 := by sorry

end ShorAlgorithms.OrderFinding
