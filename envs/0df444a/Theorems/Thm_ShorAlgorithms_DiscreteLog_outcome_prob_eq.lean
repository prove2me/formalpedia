-- Prove2me | Theorems.Thm_ShorAlgorithms_DiscreteLog_outcome_prob_eq
-- name    : ShorAlgorithms.DiscreteLog.outcome_prob_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T01:05:18.951186+00:00
-- url     : https://prove2.me/theorems/cc8714b7-6fcf-49da-aa44-c6ad71b2a59c
-- title:
--   §6, eq. (6.4) — probability of observing $|c,d,y\rangle$ with $y\equiv g^k$
-- statement:
--   Throughout, $p$ is a prime, $g$ is a generator of the multiplicative group $(\mathbb Z/p\mathbb Z)^\times$ (an element of order $p-1$), $r$ is an integer with $0\le r<p-1$ and $x=g^r$ (so $r$ is the discrete logarithm of $x$), and $q=2^l$ is a power of $2$ with $p<q<2p$.
--
--   Measure the final state (6.3) of the discrete-logarithm algorithm, obtained by applying the Fourier transform $A_q$ to each of the first two registers of the state (6.1). For $0\le c,d<q$ and $0\le k<p-1$, the probability of observing $|c,d,y\rangle$ with $y\equiv g^k\pmod p$ is
--
--   $$
--   \left|\frac{1}{(p-1)q}\sum_{\substack{0\le a,b\le p-2\\ a-rb\equiv k\ (\mathrm{mod}\ p-1)}}\exp\!\left(\frac{2\pi i}{q}(ac+bd)\right)\right|^2 .
--   $$
--
--   This identifies the output distribution with an explicit exponential sum, the starting point for every probability estimate in the analysis.
--
--   **Formalization Note** The congruence $a-rb\equiv k$ is taken in $\mathbb Z$ modulo $p-1$ (`Int.ModEq`), with $a,b$ ranging over $\{0,\dots,p-2\}$; the prefactor uses $(p-1)$ computed in $\mathbb C$. The generator is encoded as `orderOf g = p - 1`; $q$ is given as $2^l$ together with $p<q<2p$.
-- source:
--   Shor, Polynomial-Time Algorithms for Prime Factorization and Discrete Logarithms on a Quantum Computer, SIAM J. Comput. 26(5) (1997), p. 1502, §6, eq. (6.4)

import Mathlib
import Definitions.Def_ShorAlgorithms_DiscreteLog_outcomeProb

namespace ShorAlgorithms.DiscreteLog

/-- Shor (1997), §6, eq. (6.4), p. 1502: with `p` prime, `g` a generator of `(ℤ/p)ˣ`,
`x = g^r` (`0 ≤ r < p - 1`) and `q = 2^l` with `p < q < 2p`, the probability of observing
`|c, d, y⟩` with `y = g^k` (`0 ≤ k < p - 1`) is
`|(1/((p-1)q)) ∑_{a,b ∈ [0,p-2], a - r b ≡ k (mod p-1)} exp(2πi(ac + bd)/q)|²`. -/
theorem outcome_prob_eq (p : ℕ) [hp : Fact p.Prime] (g : (ZMod p)ˣ) (hg : orderOf g = p - 1)
    (r : ℕ) (hr : r < p - 1) (q l : ℕ) (hq : q = 2 ^ l) (hpq : p < q) (hqp : q < 2 * p)
    (c d : Fin q) (k : ℕ) (hk : k < p - 1) :
    outcomeProb p g (g ^ r) q c d (g ^ k) =
      ‖(1 / (((p : ℂ) - 1) * (q : ℂ))) *
        ∑ a ∈ Finset.range (p - 1), ∑ b ∈ Finset.range (p - 1),
          if (a : ℤ) - (r : ℤ) * (b : ℤ) ≡ (k : ℤ) [ZMOD ((p : ℤ) - 1)] then
            Complex.exp (2 * Real.pi * Complex.I / (q : ℂ) *
              ((a : ℂ) * ((c : ℕ) : ℂ) + (b : ℂ) * ((d : ℕ) : ℂ)))
          else 0‖ ^ 2 := by sorry

end ShorAlgorithms.DiscreteLog
