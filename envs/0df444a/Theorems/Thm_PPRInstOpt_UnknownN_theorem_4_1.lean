-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_theorem_4_1
-- name    : PPRInstOpt.UnknownN.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:15:21.265174+00:00
-- url     : https://prove2.me/theorems/194f8cb0-b393-4dfe-9ad0-e1374505c9ea
-- title:
--   Theorem 4.1 — TriPPR without knowledge of n: correct w.p. ≥ 3/4 in expected time Õ(T*)
-- statement:
--   Fix $\alpha,\varepsilon_r\in(0,1)$. There is a constant $C>0$ depending only on $\alpha$ and $\varepsilon_r$ such that on every valid instance $(G,s,t)$ with $n$ vertices and $\pi(s,t)>0$, TriPPR$(s,t,\varepsilon_r)$, which is not given $n$, halts with probability one, its estimate satisfies
--   $$\Pr\big\{|\hat\pi(s,t)-\pi(s,t)|\le\varepsilon_r\,\pi(s,t)\big\}\ge\frac34,$$
--   and its expected running time is at most $C\,T^*\log n$.
--
--   Differences from the source:
--   - reading: expected running time Õ(T*) → ≤ C T* log n with C depending only on α and εr; reason: §4 opens 'show that its expected running time is O(T* log n)' (p. 23), which Lemmas 4.4–4.5 give
--   - reading: (implicit) TriPPR terminates → explicit clause: the non-halting set has probability 0; reason: implied by the finite expected time, since time is ⊤ off halting
--   - reading: §4 tacitly assumes t is reachable from s → hypothesis 0 < π(s, t); reason: T* divides by π(s, t) and Lemma 4.3 fails at π(s, t) = 0 (finding I2)
--   - encoding: the algorithm is not given n → TriPPR is generic in the vertex type (no Fintype instance), sees the graph only through the Oracle and the vertices s, t; reason: it cannot enumerate V, probe unseen labels or learn n
--   - encoding: independent random walks; X1, X2, X3 independent; rounds independent → one tape of i.i.d. uniform [0, 1] entries (tapeLaw), read as independent streams; call γ of round i reads stream (i, γ); reason: the paper's randomness; independence by disjoint coordinates
--   - encoding: unit-cost RAM with Θ(log n)-bit words and O(log n)-bit floating point (§1.4, §3.3) → exact real arithmetic; time is the `cost` field, one unit per primitive, with the §3.3 heap bookkeeping charged at its binary-heap cost; reason: reading of §1.4; the floating-point error paragraph of §3.3 is not formalized
--   - reading: εr a constant relative error → 0 < εr < 1; reason: εr ≥ 1 makes the output 0 always correct; the paper's constant-factor estimation needs εr < 1
--   - reading: candidate set {u ∈ V \ F : threshold} ∪ (C^(ℓ−1) \ F) → only vertices with positive residue are activated; reason: finding I1: with threshold 0 the printed set contains unreached vertices, not computable without n; for a positive threshold the sets coincide
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 24, Theorem 4.1

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_QueryModel

open MeasureTheory
open scoped ENNReal

namespace PPRInstOpt.UnknownN

/-- Theorem 4.1 (p. 24): `TriPPR(s, t, εr)`, which is not given `n`, halts with probability one and
outputs `\hat π(s, t)` with `Pr{|\hat π(s, t) - π(s, t)| ≤ εr π(s, t)} ≥ 3/4`; its expected running
time is `Õ(T*)`, read as `O(T* log n)` with a constant depending only on `α` and `εr`. -/
theorem theorem_4_1 (α εr : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < εr) (hε1 : εr < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) (s t : V), 0 < ppr α G s t →
        tapeLaw {ω | ¬ triHalts G.oracle α εr s t ω} = 0 ∧
        (3 / 4 : ℝ≥0∞) ≤ tapeLaw {ω | triHalts G.oracle α εr s t ω ∧
          |triOutput G.oracle α εr s t ω - ppr α G s t| ≤ εr * ppr α G s t} ∧
        triExpTime α εr G s t ≤
          ENNReal.ofReal (C * Tstar α G s t * Real.log (Fintype.card V)) := by sorry

end PPRInstOpt.UnknownN
