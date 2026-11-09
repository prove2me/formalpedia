-- Prove2me | Theorems.Thm_QueryDepthMIS_lemma_2_9
-- name    : QueryDepthMIS.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:32:36.860475+00:00
-- url     : https://prove2.me/theorems/ab142f97-efca-44dc-bdc2-68ce2ad61036
-- title:
--   Lemma 2.9 — degree reduction: $\Pr[\Delta(G_{\mathrm{alive}}(t+1,n)) \ge d] \le n e^{-td/n}$
-- statement:
--   Let $G$ be a simple graph on $n$ vertices and $\pi$ a uniformly random permutation of its vertices. For every integer $1 \le t < n$:
--
--   1. for every real $d > 0$,
--   $$
--   \Pr\big[\Delta(G_{\mathrm{alive}}(t + 1, n)) \ge d\big] \le n \exp(-td/n);
--   $$
--   2. with probability at least $1 - 1/n^7$,
--   $$
--   \Delta(G_{\mathrm{alive}}(t + 1, n)) \le \frac{8 n \ln n}{t}.
--   $$
--
--   After $t$ steps of the greedy process every surviving vertex has few surviving neighbours; this is what makes the conditions of the hop lemmas and the degree bound in the proof of Theorem 3.1 hold.
--
--   Differences from the source:
--   - encoding: a uniformly random permutation π of V, π(i) the i-th vertex → the uniform (counting) law on orderings ω : V ≃ Fin n, π = ω⁻¹, with 1-based ranks rank ω v = ω v + 1; reason: the same law; positions keep the paper's 1-based values
--   - encoding: a simple graph G with no order on V → an additional instance [LinearOrder V]; reason: required by the reused RGMISFast.tau to break rank ties; ranks of a permutation are injective, so it never acts
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 2.9, p.9

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_QueryDepthMIS_aliveSet
import Definitions.Def_QueryDepthMIS_maxDegOn
import Definitions.Def_QueryDepthMIS_rank

set_option autoImplicit false

namespace QueryDepthMIS

/-- Lemma 2.9 (Degree reduction bound [BFS12]) (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 2.9, p.9): "For every integer
1 ≤ t < n and real d > 0, Pr[Δ(G_alive(t + 1, n)) ≥ d] ≤ n exp(−td/n). Consequently, this degree
is at most 8n ln n/t with probability at least 1 − 1/n⁷."

For every simple graph `G` on `n = |V|` vertices and every integer `1 ≤ t < n`: (1) for every real
`d > 0`, the probability over a uniformly random permutation that `Δ(G_alive(t + 1, n)) ≥ d` is at
most `n·exp(−td/n)`; (2) `Δ(G_alive(t + 1, n)) ≤ 8n ln n / t` with probability at least
`1 − 1/n⁷`.

**Formalization Note** `G_alive(t + 1, n)` is `aliveSet G (rank ω) (t + 1) n`, its maximum degree
`maxDegOn`; `ln` is `Real.log`. `[LinearOrder V]` is the tie-breaker required by
`RGMISFast.tau`; ranks are injective, so it is never used. -/
theorem lemma_2_9 :
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ),
      1 ≤ t → t < Fintype.card V →
      (∀ d : ℝ, 0 < d →
        PunctSketch.coinProb (fun ω : Perm V =>
          d ≤ (maxDegOn G (aliveSet G (rank ω) (t + 1) (Fintype.card V)) : ℝ)) ≤
          (Fintype.card V : ℝ) * Real.exp (-((t : ℝ) * d) / (Fintype.card V : ℝ))) ∧
      1 - 1 / (Fintype.card V : ℝ) ^ 7 ≤
        PunctSketch.coinProb (fun ω : Perm V =>
          (maxDegOn G (aliveSet G (rank ω) (t + 1) (Fintype.card V)) : ℝ) ≤
            8 * (Fintype.card V : ℝ) * Real.log (Fintype.card V : ℝ) / (t : ℝ)) := by sorry

end QueryDepthMIS
