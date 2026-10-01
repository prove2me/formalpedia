-- Prove2me | Theorems.Thm_ShorAlgorithms_DiscreteLog_good_output_prob_ge
-- name    : ShorAlgorithms.DiscreteLog.good_output_prob_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T01:32:51.197036+00:00
-- url     : https://prove2.me/theorems/986beb3b-a80b-4734-aee4-039d67b0b5aa
-- title:
--   §6, p. 1504 — the discrete-log circuit gives a good output with probability at least $1/480$
-- statement:
--   Throughout, $p$ is a prime, $g$ is a generator of the multiplicative group $(\mathbb Z/p\mathbb Z)^\times$ (an element of order $p-1$), $r$ is an integer with $0\le r<p-1$ and $x=g^r$ (so $r$ is the discrete logarithm of $x$), and $q=2^l$ is a power of $2$ with $p<q<2p$.
--
--   Run Shor's discrete-logarithm circuit: prepare the state
--
--   $$
--   \frac{1}{p-1}\sum_{a=0}^{p-2}\sum_{b=0}^{p-2}|a,b,g^ax^{-b}\ (\mathrm{mod}\ p)\rangle,
--   $$
--
--   apply the Fourier transform $A_q$ (entries $q^{-1/2}e^{2\pi i ac/q}$) to each of the first two registers, and measure all three registers, obtaining $|c,d,y\rangle$. The output is *good* if $(c,d)$ satisfies (6.10) $|\{T\}_q|\le\frac12$ with $T=rc+d-\frac{r}{p-1}\{c(p-1)\}_q$, and (6.11) $|\{c(p-1)\}_q|\le q/12$. Then
--
--   $$
--   \Pr[\text{the observed output is good}]\ \ge\ \frac{1}{480}.
--   $$
--
--   This constant success probability is what makes the quantum discrete-logarithm algorithm run in expected polynomial time: from a few good outputs the discrete logarithm $r$ can be deduced.
--
--   **Formalization Note** The paper states the intermediate bound "at least $p/(240q)$"; its own count gives $(p-1)/(240q)$, which still yields $1/480$ because $q$ and $2p$ are both even, so $q<2p$ forces $q\le2(p-1)$. Only $1/480$ is stated. The state preparation by testing and restarting is not formalized; the state (6.1) is taken as given.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1504, §6 ("… the probability of observing some good state is at least $p/(240q)$, or at least $1/480$ (since $q < 2p$).")

import Mathlib
import Definitions.Def_ShorAlgorithms_DiscreteLog_outcomeProb
import Definitions.Def_ShorAlgorithms_DiscreteLog_IsGood

namespace ShorAlgorithms.DiscreteLog

open Classical in
/-- Shor (1997), §6, p. 1504 ("the probability of observing some good state is … at least
1/480"): for every prime `p`, generator `g` of `(ℤ/p)ˣ`, discrete logarithm `r` with
`0 ≤ r < p - 1` (`x = g^r`), and `q = 2^l` with `p < q < 2p`, the probability that the observed
state `|c, d, y⟩` of the discrete-logarithm circuit is good ((6.10) and (6.11)) is at least
`1/480`. -/
theorem good_output_prob_ge (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (r : ℕ) (hr : r < p - 1) (q l : ℕ) (hq : q = 2 ^ l) (hpq : p < q) (hqp : q < 2 * p) :
    (1 : ℝ) / 480 ≤ ∑ c : Fin q, ∑ d : Fin q,
      if IsGood p q r c d then ∑ y : (ZMod p)ˣ, outcomeProb p g (g ^ r) q c d y else 0 := by sorry

end ShorAlgorithms.DiscreteLog
