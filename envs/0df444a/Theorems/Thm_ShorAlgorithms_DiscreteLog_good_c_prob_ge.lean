-- Prove2me | Theorems.Thm_ShorAlgorithms_DiscreteLog_good_c_prob_ge
-- name    : ShorAlgorithms.DiscreteLog.good_c_prob_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T01:25:43.034478+00:00
-- url     : https://prove2.me/theorems/689269cf-29e3-408d-bf01-a6cbe69c490e
-- title:
--   §6, p. 1504 — each good $c$ is observed with probability at least $(p-1)/(20q^2)\ge 1/(40q)$
-- statement:
--   Throughout, $p$ is a prime, $g$ is a generator of the multiplicative group $(\mathbb Z/p\mathbb Z)^\times$ (an element of order $p-1$), $r$ is an integer with $0\le r<p-1$ and $x=g^r$ (so $r$ is the discrete logarithm of $x$), and $q=2^l$ is a power of $2$ with $p<q<2p$.
--
--   Call $0\le c<q$ *good* if $(c,d)$ satisfies (6.10) and (6.11) for some $0\le d<q$. Then, when the final state (6.3) is measured, the first register shows a good $c$ with probability at least $(p-1)/(20q^2)$, and this is at least $1/(40q)$:
--
--   $$
--   \sum_{d=0}^{q-1}\ \sum_{y\in(\mathbb Z/p)^\times}\Pr[c,d,y]\ \ge\ \frac{p-1}{20q^2}\ \ge\ \frac{1}{40q}.
--   $$
--
--   This is the form of the success probability used when recovering $r$ from several good values $c$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1504, §6 ("Note that each good $c$ has a probability of at least …")

import Mathlib
import Definitions.Def_ShorAlgorithms_DiscreteLog_outcomeProb
import Definitions.Def_ShorAlgorithms_DiscreteLog_IsGood

namespace ShorAlgorithms.DiscreteLog

/-- Shor (1997), §6, p. 1504 ("Note that each good `c`"): under the hypotheses of §6, a value
`c` that forms a good pair `(c, d)` with some `d` is observed in the first register with
probability (summed over all `d` and `y`) at least `(p - 1)/(20 q²)`, and `(p - 1)/(20 q²) ≥ 1/(40 q)`. -/
theorem good_c_prob_ge (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (r : ℕ) (hr : r < p - 1) (q l : ℕ) (hq : q = 2 ^ l) (hpq : p < q) (hqp : q < 2 * p)
    (c : Fin q) (hc : ∃ d : Fin q, IsGood p q r c d) :
    ((p : ℝ) - 1) / (20 * (q : ℝ) ^ 2) ≤
        ∑ d : Fin q, ∑ y : (ZMod p)ˣ, outcomeProb p g (g ^ r) q c d y ∧
      1 / (40 * (q : ℝ)) ≤ ((p : ℝ) - 1) / (20 * (q : ℝ) ^ 2) := by sorry

end ShorAlgorithms.DiscreteLog
