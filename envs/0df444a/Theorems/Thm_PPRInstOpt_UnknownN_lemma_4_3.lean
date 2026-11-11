-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_lemma_4_3
-- name    : PPRInstOpt.UnknownN.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:14:21.012202+00:00
-- url     : https://prove2.me/theorems/0a6c3653-c31a-4a95-95ca-437a1409f7ef
-- title:
--   Lemma 4.3 — TriPPR's output has relative error ≥ εr with probability ≤ 1/4
-- statement:
--   On a valid instance with $\pi(s,t)>0$, the output $X_3^{(i^R)}$ of TriPPR$(s,t,\varepsilon_r)$ satisfies
--   $$\Pr\big\{|X_3^{(i^R)}-\pi(s,t)|\ge\varepsilon_r\,\pi(s,t)\big\}\le\frac14,$$
--   where a run that does not halt counts as a failure.
--
--   Differences from the source:
--   - reading: §4 tacitly assumes t is reachable from s → hypothesis 0 < π(s, t); reason: T* divides by π(s, t) and Lemma 4.3 fails at π(s, t) = 0 (finding I2)
--   - reading: the event |X_3^(i^R) − π(s, t)| ≥ εr π(s, t) → the event 'TriPPR does not halt, or |X_3^(i^R) − π(s, t)| ≥ εr π(s, t)'; reason: X_3^(i^R) exists only when TriPPR halts; counting non-halting as failure is the stronger reading
--   - encoding: independent random walks; X1, X2, X3 independent; rounds independent → one tape of i.i.d. uniform [0, 1] entries (tapeLaw), read as independent streams; call γ of round i reads stream (i, γ); reason: the paper's randomness; independence by disjoint coordinates
--   - encoding: the algorithm is not given n → TriPPR is generic in the vertex type (no Fintype instance), sees the graph only through the Oracle and the vertices s, t; reason: it cannot enumerate V, probe unseen labels or learn n
--   - encoding: unit-cost RAM with Θ(log n)-bit words and O(log n)-bit floating point (§1.4, §3.3) → exact real arithmetic; time is the `cost` field, one unit per primitive, with the §3.3 heap bookkeeping charged at its binary-heap cost; reason: reading of §1.4; the floating-point error paragraph of §3.3 is not formalized
--   - reading: εr a constant relative error → 0 < εr < 1; reason: εr ≥ 1 makes the output 0 always correct; the paper's constant-factor estimation needs εr < 1
--   - reading: candidate set {u ∈ V \ F : threshold} ∪ (C^(ℓ−1) \ F) → only vertices with positive residue are activated; reason: finding I1: with threshold 0 the printed set contains unreached vertices, not computable without n; for a positive threshold the sets coincide
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 27, Lemma 4.3

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_TriPPR

open MeasureTheory
open scoped ENNReal

namespace PPRInstOpt.UnknownN

/-- Lemma 4.3 (p. 27), on the valid instances of §4 (`π(s, t) > 0`): the probability that
`TriPPR(s, t, εr)` does not output an `X_3^(i^R)` with `|X_3^(i^R) - π(s, t)| < εr π(s, t)` is at
most `1/4`. -/
theorem lemma_4_3 {V : Type} [Fintype V] [DecidableEq V] (α εr : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hε0 : 0 < εr) (hε1 : εr < 1) (G : Digraph V) (s t : V) (hpos : 0 < ppr α G s t) :
    tapeLaw {ω | ¬ triHalts G.oracle α εr s t ω ∨
      εr * ppr α G s t ≤ |triOutput G.oracle α εr s t ω - ppr α G s t|} ≤ 1 / 4 := by sorry

end PPRInstOpt.UnknownN
