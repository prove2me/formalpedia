-- Prove2me | Theorems.Thm_ShorAlgorithms_OrderFinding_card_good_outcomes_ge
-- name    : ShorAlgorithms.OrderFinding.card_good_outcomes_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T09:35:11.529068+00:00
-- url     : https://prove2.me/theorems/64051adc-efa3-42b9-9fe3-38cab85b03c1
-- title:
--   §5, p. 1501 — at least $\varphi(r)$ values of $c$ are good, and each one gives $r$
-- statement:
--   Let $n > 1$, let $x$ be coprime to $n$ with multiplicative order $r$ modulo $n$, and let $q = 2^l$ satisfy $n^2 \le q < 2n^2$. Call $c \in \{0, \dots, q-1\}$ **good** if there is $0 \le d < r$ with $\gcd(d, r) = 1$ and
--
--   $$
--   \left|\frac{c}{q} - \frac{d}{r}\right| \le \frac{1}{2q}.
--   $$
--
--   Then:
--
--   1. there are at least $\varphi(r)$ good values of $c$, where $\varphi$ is Euler's totient function;
--   2. the powers $x^k \bmod n$, $0 \le k < r$, take exactly $r$ distinct values, so there are at least $r\varphi(r)$ states $|c, x^k \bmod n\rangle$ with $c$ good;
--   3. every good $c$ gives us $r$: rounding $c/q$ to the nearest fraction with denominator smaller than $n$ returns a fraction with denominator $r$ in lowest terms;
--   4. every good $c$ satisfies (5.12): $-r/2 \le rc - d'q \le r/2$ for some integer $d'$.
--
--   Together with the per-state bound $1/3r^2$, this gives at least $r\varphi(r)$ outcomes $|c, x^k\rangle$, each of probability at least $1/3r^2$ and each of which yields $r$.
--
--   **Formalization Note** "Gives us $r$" is `yieldsOrder n q r c`. At $r = 1$ the only $d$ is $d = 0$ (since $\gcd(0,1) = 1$), matching $\varphi(1) = 1$. The hypothesis $n > 1$ excludes $n = 1$, where no fraction has denominator smaller than $n$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), pp. 1500–1501, §5, "There are φ(r) possible values of d relatively prime to r … which would enable us to obtain r"

import Mathlib
import Definitions.Def_ShorAlgorithms_OrderFinding_yieldsOrder

namespace ShorAlgorithms.OrderFinding

open Classical in
/-- Shor (1997), §5, pp. 1500–1501: the count of good observations. Let `n > 1`, `x` coprime
to `n` with order `r`, and `q = 2^l` with `n² ≤ q < 2n²`. Call `c ∈ {0, …, q-1}` *good* if
`|c/q - d/r| ≤ 1/(2q)` for some `0 ≤ d < r` relatively prime to `r`. Then
1. there are at least `φ(r)` good values of `c`;
2. there are `r` possible values `x^k (mod n)`, `0 ≤ k < r`, so there are at least `r φ(r)`
   states `|c, x^k (mod n)⟩` with `c` good; and
3. every good `c` gives us `r` by rounding (`yieldsOrder n q r c`) and satisfies (5.12),
   `-r/2 ≤ rc - d'q ≤ r/2` for an integer `d'`. -/
theorem card_good_outcomes_ge (n x q l : ℕ) (hn : 1 < n) (hx : Nat.Coprime x n)
    (hq : q = 2 ^ l) (hnq : n ^ 2 ≤ q) (hq2 : q < 2 * n ^ 2) :
    Nat.totient (orderOf (x : ZMod n)) ≤
        ((Finset.univ : Finset (Fin q)).filter (fun c : Fin q => ∃ d : ℕ, d < orderOf (x : ZMod n) ∧
          Nat.Coprime d (orderOf (x : ZMod n)) ∧
          |((c : ℕ) : ℝ) / q - (d : ℝ) / (orderOf (x : ZMod n) : ℝ)| ≤ 1 / (2 * q))).card ∧
    ((Finset.range (orderOf (x : ZMod n))).image (fun k : ℕ => (x : ZMod n) ^ k)).card =
        orderOf (x : ZMod n) ∧
    orderOf (x : ZMod n) * Nat.totient (orderOf (x : ZMod n)) ≤
        (((Finset.univ : Finset (Fin q)).filter (fun c : Fin q => ∃ d : ℕ, d < orderOf (x : ZMod n) ∧
          Nat.Coprime d (orderOf (x : ZMod n)) ∧
          |((c : ℕ) : ℝ) / q - (d : ℝ) / (orderOf (x : ZMod n) : ℝ)| ≤ 1 / (2 * q))) ×ˢ
          ((Finset.range (orderOf (x : ZMod n))).image (fun k : ℕ => (x : ZMod n) ^ k))).card ∧
    ∀ c : Fin q, (∃ d : ℕ, d < orderOf (x : ZMod n) ∧ Nat.Coprime d (orderOf (x : ZMod n)) ∧
          |((c : ℕ) : ℝ) / q - (d : ℝ) / (orderOf (x : ZMod n) : ℝ)| ≤ 1 / (2 * q)) →
      yieldsOrder n q (orderOf (x : ZMod n)) (c : ℕ) ∧
        ∃ d : ℤ,
          -((orderOf (x : ZMod n) : ℝ) / 2) ≤
            (orderOf (x : ZMod n) : ℝ) * ((c : ℕ) : ℝ) - (d : ℝ) * (q : ℝ) ∧
          (orderOf (x : ZMod n) : ℝ) * ((c : ℕ) : ℝ) - (d : ℝ) * (q : ℝ) ≤
            (orderOf (x : ZMod n) : ℝ) / 2 := by sorry

end ShorAlgorithms.OrderFinding
