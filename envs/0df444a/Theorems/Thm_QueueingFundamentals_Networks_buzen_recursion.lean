-- Prove2me | Theorems.Thm_QueueingFundamentals_Networks_buzen_recursion
-- name    : QueueingFundamentals.Networks.buzen_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T09:10:51.880989+00:00
-- url     : https://prove2.me/theorems/f64ccc10-7f21-456d-ad13-6758758be25c
-- title:
--   Eqs. (4.19)–(4.21) — Buzen's convolution algorithm for G(N)
-- statement:
--   Consider a closed network of $k$ nodes, node $i$ having $c_i \ge 1$ servers, with numbers $\rho_1, \dots, \rho_k$, and let
--   $$f_i(n) = \frac{\rho_i^{\,n}}{a_i(n)}, \qquad a_i(n) = \begin{cases} n! & (n < c_i),\\ c_i^{\,n-c_i}\,c_i! & (n \ge c_i),\end{cases}$$
--   $$G(N) = \sum_{n_1+\cdots+n_k=N}\prod_{i=1}^{k} f_i(n_i), \qquad g_m(n) = \sum_{n_1+\cdots+n_m=n}\prod_{i=1}^{m} f_i(n_i) \quad (0 \le m \le k).$$
--   Then
--   1. $G(N) = g_k(N)$;
--   2. for $1 \le m \le k$ and $n \ge 0$,
--   $$g_m(n) = \sum_{i=0}^{n} f_m(i)\, g_{m-1}(n - i);$$
--   3. $g_1(n) = f_1(n)$;
--   4. $g_m(0) = 1$.
--
--   The recursion computes $G(N)$ with $O(kN^2)$ arithmetic operations instead of a sum over the $\binom{N+k-1}{N}$ states, and the intermediate values $g_m(n)$ also give marginal distributions (4.22).
--
--   **Formalization Note** $g_m$ is defined by the sum (4.20), so the recursion is a statement, not a definition. Node $m$ of the book is index $m-1$ of `Fin k`; $g_0$ is the empty-network constant ($1$ at $n = 0$, $0$ otherwise).
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.198–199, Eqs. (4.19), (4.20), (4.21) and the note following (4.21); p.191, Eq. (4.13)

import Mathlib
import Definitions.Def_QueueingFundamentals_Networks_ClosedJackson

namespace QueueingFundamentals.Networks

open Finset

/-- Eqs. (4.19)–(4.21), pp.198–199 (Buzen's algorithm): with `f_i(n) = ρ_i^n / a_i(n)` for a closed
network with `c_i ≥ 1` servers at node `i`,
(1) `G(N) = g_k(N)`;
(2) `g_m(n) = ∑_{i=0}^{n} f_m(i) g_{m−1}(n − i)` for `1 ≤ m ≤ k` (node `m` is index `m − 1`);
(3) `g_1(n) = f_1(n)`;
(4) `g_m(0) = 1`. -/
theorem buzen_recursion {k : ℕ} (rho : Fin k → ℝ) (c : Fin k → ℕ) (hc : ∀ i, 1 ≤ c i) :
    (∀ N : ℕ, normConst (buzenFactor rho c) N = gBuzen (buzenFactor rho c) k le_rfl N) ∧
    (∀ (m : ℕ) (hm : m + 1 ≤ k) (n : ℕ),
      gBuzen (buzenFactor rho c) (m + 1) hm n =
        ∑ i ∈ range (n + 1),
          buzenFactor rho c ⟨m, hm⟩ i * gBuzen (buzenFactor rho c) m (Nat.le_of_succ_le hm) (n - i)) ∧
    (∀ (h1 : 1 ≤ k) (n : ℕ), gBuzen (buzenFactor rho c) 1 h1 n = buzenFactor rho c ⟨0, h1⟩ n) ∧
    (∀ (m : ℕ) (hm : m ≤ k), gBuzen (buzenFactor rho c) m hm 0 = 1) := by sorry

end QueueingFundamentals.Networks
