-- Prove2me | Theorems.Thm_SupplyChainTheory_long_chain_open_chain
-- name    : SupplyChainTheory.long_chain_open_chain
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:12:49.732144+00:00
-- url     : https://prove2.me/theorems/aaf8a123-9966-494c-805e-a59ee69e5696
-- title:
--   Lemma 7.8: $[C_n] = n\big([L_n] - [L_{n-1}]\big)$
-- statement:
--   **Lemma 7.8.** For any balanced system of size $n \ge 1$ with exchangeable demand,
--
--   $$ [C_n] \;=\; n\big([L_n] - [L_{n-1}]\big), $$
--
--   where $[L_k]$ is the expected performance of the open chain on the subsystem of products and
--   plants $1, \dots, k$, whose demand is the corresponding marginal of $D$. The proof is the
--   realization-level identity (7.30) of Simchi-Levi and Wei,
--   $P(d, C_n) = \sum_{i=1}^n \big(P(d, C_n \setminus \{(i+1, i)\}) - P(d, C_n \setminus \{(i, i-1), (i, i), (i+1, i)\})\big)$,
--   in which removing one flexible edge from the cycle leaves an open chain of length $n$ and
--   removing two consecutive flexible edges with the dedicated edge between them leaves an open
--   chain of length $n - 1$, all relabelings having the same expectation by exchangeability. The
--   lemma expresses the long chain through open chains, which are far easier to evaluate.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 251, Sect. 7.5.3, Lemma 7.8 and its proof, Eq. (7.30); after Simchi-Levi and Wei (2012), Theorem 3

import Definitions.Def_SupplyChainTheory_flexibility

namespace SupplyChainTheory

theorem long_chain_open_chain {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] {n : ℕ} (S : BalancedSystem P n) (hn : 0 < n) :
    S.expPerf (longChain n)
      = n * (S.subPerf n (openChain n) - S.subPerf (n - 1) (openChain (n - 1))) := by sorry

end SupplyChainTheory
