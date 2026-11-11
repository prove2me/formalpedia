-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_lemma_4_4
-- name    : PPRInstOpt.UnknownN.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:15:42.506009+00:00
-- url     : https://prove2.me/theorems/24726ca1-5655-4553-9f76-ec667698a231
-- title:
--   Lemma 4.4 — the expected time of TriPPR is O(2^{i*})
-- statement:
--   There is a constant $C>0$ depending only on $\alpha$ and $\varepsilon_r$ such that on every valid instance with $\pi(s,t)>0$
--   $$\mathbb E[\text{time of TriPPR}(s,t,\varepsilon_r)]\le C\,2^{i^*},$$
--   where $i^*$ is the least round $i\ge1$ with $\tau^{(i)}\le 32\,\pi(s,t)$ (Eq. (20)).
--
--   Differences from the source:
--   - encoding: O(2^{i*}) → ∃ C > 0 depending only on α and εr; reason: explicit constant
--   - encoding: i* = smallest integer i with τ^(i) ≤ 32 π(s, t) → smallest i ≥ 1; reason: τ^(0) = 1024/εr² > 32 π(s, t), so i* ≥ 1 anyway
--   - reading: §4 tacitly assumes t is reachable from s → hypothesis 0 < π(s, t); reason: T* divides by π(s, t) and Lemma 4.3 fails at π(s, t) = 0 (finding I2)
--   - encoding: independent random walks; X1, X2, X3 independent; rounds independent → one tape of i.i.d. uniform [0, 1] entries (tapeLaw), read as independent streams; call γ of round i reads stream (i, γ); reason: the paper's randomness; independence by disjoint coordinates
--   - encoding: the algorithm is not given n → TriPPR is generic in the vertex type (no Fintype instance), sees the graph only through the Oracle and the vertices s, t; reason: it cannot enumerate V, probe unseen labels or learn n
--   - encoding: unit-cost RAM with Θ(log n)-bit words and O(log n)-bit floating point (§1.4, §3.3) → exact real arithmetic; time is the `cost` field, one unit per primitive, with the §3.3 heap bookkeeping charged at its binary-heap cost; reason: reading of §1.4; the floating-point error paragraph of §3.3 is not formalized
--   - reading: εr a constant relative error → 0 < εr < 1; reason: εr ≥ 1 makes the output 0 always correct; the paper's constant-factor estimation needs εr < 1
--   - reading: candidate set {u ∈ V \ F : threshold} ∪ (C^(ℓ−1) \ F) → only vertices with positive residue are activated; reason: finding I1: with threshold 0 the printed set contains unreached vertices, not computable without n; for a positive threshold the sets coincide
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 28, Lemma 4.4

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_QueryModel

open MeasureTheory
open scoped ENNReal

namespace PPRInstOpt.UnknownN

/-- Lemma 4.4 (p. 28): there is a constant `C` depending only on `α` and `εr` such that on every
valid instance the expected running time of Algorithm 8 is at most `C 2^{i*}`. -/
theorem lemma_4_4 (α εr : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < εr) (hε1 : εr < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) (s t : V), 0 < ppr α G s t →
        triExpTime α εr G s t ≤ ENNReal.ofReal (C * 2 ^ istar α εr G s t) := by sorry

end PPRInstOpt.UnknownN
