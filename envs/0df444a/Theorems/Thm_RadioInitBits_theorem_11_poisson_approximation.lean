-- Prove2me | Theorems.Thm_RadioInitBits_theorem_11_poisson_approximation
-- name    : RadioInitBits.theorem_11_poisson_approximation
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:10:56.395399+00:00
-- url     : https://prove2.me/theorems/2ac603b4-5518-4686-902d-a9047c126937
-- title:
--   Theorem 11 — Poisson approximation of balls in bins: true probability $\le p\,e\sqrt m$ (corrected: $m\ge1$)
-- statement:
--   Throw $m\ge1$ balls independently and uniformly at random into $N$ bins. Let $A$ be any set of load vectors. Let $p$ be the probability of $A$ when the loads of the $N$ bins are replaced by independent Poisson random variables with mean $m/N$. Then the true probability that the load vector lies in $A$ is at most $p\,e\sqrt m$:
--   $$\Pr_{\text{exact}}[L\in A]\ \le\ e\sqrt m\;\sum_{a\in A}\prod_{j=1}^{N}\frac{e^{-m/N}(m/N)^{a_j}}{a_j!}.$$
--
--   The paper uses this bound to transfer tail bounds from independent Poisson loads to the true, dependent loads. It does so in the analysis of each phase (proof of Lemma 30) and in the proof of Theorem 5. The transfer costs a factor $O(\sqrt m)$ in the failure probability.
--
--   **Formalization Note** The exact probability is the fraction of the $N^m$ equally likely throws whose load vector lies in $A$. Any number $N$ of bins is allowed.
--
--   Differences from the source:
--   - correction: "If m balls are thrown …" for every m → m ≥ 1; reason: at m = 0 the event A = {all loads 0} has Poisson probability p = 1 and true probability 1, but the bound p·e·√0 = 0; m ≥ 1 is the hypothesis of the cited source (Mitzenmacher–Upfal, Corollary 5.9)
--   - reading: the first sentence ("the distribution of the number of balls in a given bin is approximately Poisson with mean m/n") → not formalized; reason: it has no quantitative content, and the "Moreover" clause is the theorem's claim
-- source:
--   Banasik, Dani, Hayes, Initialization with Exponentially Fewer Bits, STOC 2027 submission (manuscript, sha256 859ca50d…), full version Theorem 11, p.6 (PDF p.27), rephrased from Mitzenmacher–Upfal, Probability and Computing, §5.4 (Corollary 5.9)

import Mathlib
import Definitions.Def_RadioInitBits_exactLoadProb

set_option autoImplicit false

namespace RadioInitBits

open scoped ENNReal

/-- **Theorem 11** (Poisson approximation, the "Moreover" clause), corrected to `m ≥ 1`.
If `m ≥ 1` balls are thrown independently and uniformly at random into `N` bins, then every event
`A` about the load vector that has probability `p` when the loads are replaced by independent
Poisson random variables with mean `m / N` has true probability at most `p · e · √m`.
D. Banasik, V. Dani, T. P. Hayes, *Initialization with Exponentially Fewer Bits*, STOC 2027
submission (held version, sha256 859ca50d…), full version Theorem 11, p.6 (PDF p.27), rephrased
from Mitzenmacher–Upfal, §4.2 of *Probability and Computing* (their Corollary 5.9).

**Formalization Note** The source states the bound for every `m`; at `m = 0` it is false
(`A = {all loads 0}`: Poisson probability `1`, bound `1 · e · √0 = 0`, true probability `1`), so
`m ≥ 1` (the hypothesis of the cited Corollary 5.9) is added. The first sentence of Theorem 11
("approximately Poisson") has no quantitative content and is not formalized. Any number of bins
`N` is allowed (for `N = 0` and `m ≥ 1` there is no throw and the true probability is `0`). -/
theorem theorem_11_poisson_approximation (m N : ℕ) (hm : 1 ≤ m) (A : Set (Fin N → ℕ)) :
    exactLoadProb m N A ≤ ENNReal.ofReal (Real.exp 1 * Real.sqrt m) * poissonLoadProb m N A := by sorry

end RadioInitBits
