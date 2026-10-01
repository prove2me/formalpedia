-- Prove2me | Theorems.Thm_ShorAlgorithms_DiscreteLog_good_state_prob_ge
-- name    : ShorAlgorithms.DiscreteLog.good_state_prob_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T01:12:27.901796+00:00
-- url     : https://prove2.me/theorems/be927b51-0d82-40a4-b8f0-5fad4242e3e5
-- title:
--   §6, eq. (6.17) — each good state is observed with probability at least $1/(20q^2)$
-- statement:
--   Throughout, $p$ is a prime, $g$ is a generator of the multiplicative group $(\mathbb Z/p\mathbb Z)^\times$ (an element of order $p-1$), $r$ is an integer with $0\le r<p-1$ and $x=g^r$ (so $r$ is the discrete logarithm of $x$), and $q=2^l$ is a power of $2$ with $p<q<2p$.
--
--   Let $0\le c,d<q$ be such that $(c,d)$ is good, i.e. satisfies conditions (6.10) and (6.11), and let $y$ be any nonzero residue modulo $p$. Then the probability of observing $|c,d,y\rangle$ when the final state (6.3) is measured satisfies
--
--   $$
--   \Pr[c,d,y]\ \ge\ \frac{1}{20q^2}.
--   $$
--
--   This per-state lower bound, combined with a count of good pairs, gives the constant success probability of the algorithm.
--
--   **Formalization Note** The paper derives the bound from the integral approximation (6.16), whose error term $O(W/(pq))$ has an unspecified constant, and then states $1/(20q^2)$ without a threshold on $p$. The statement here is the page's unconditional claim, for every prime $p$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1504, §6, eq. (6.17) and the sentence after it ("or at least $.054/q^2 > 1/(20q^2)$")

import Mathlib
import Definitions.Def_ShorAlgorithms_DiscreteLog_outcomeProb
import Definitions.Def_ShorAlgorithms_DiscreteLog_IsGood

namespace ShorAlgorithms.DiscreteLog

/-- Shor (1997), §6, eq. (6.17), p. 1504: under the hypotheses of §6, every state `|c, d, y⟩`
whose `(c, d)` satisfies (6.10) and (6.11) is observed with probability at least `1/(20 q²)`. -/
theorem good_state_prob_ge (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (r : ℕ) (hr : r < p - 1) (q l : ℕ) (hq : q = 2 ^ l) (hpq : p < q) (hqp : q < 2 * p)
    (c d : Fin q) (hgood : IsGood p q r c d) (y : (ZMod p)ˣ) :
    1 / (20 * (q : ℝ) ^ 2) ≤ outcomeProb p g (g ^ r) q c d y := by sorry

end ShorAlgorithms.DiscreteLog
