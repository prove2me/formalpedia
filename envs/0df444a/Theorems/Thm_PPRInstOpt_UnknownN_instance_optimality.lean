-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_instance_optimality
-- name    : PPRInstOpt.UnknownN.instance_optimality
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:15:48.26087+00:00
-- url     : https://prove2.me/theorems/d7243ce0-4d49-41db-b737-4bfe9d4a5955
-- title:
--   Instance-optimality of TriPPR when n is unknown (Theorems 4.1 + 5.4)
-- statement:
--   Fix $\alpha,\varepsilon_r\in(0,1)$. There is a constant $C>0$ depending only on $\alpha$ and $\varepsilon_r$ such that on every valid instance $(G,s,t)$ — a finite simple digraph with every out-degree at least one and fixed adjacency lists, and vertices $s,t$ with $\pi(s,t)>0$ — with $n$ vertices: TriPPR$(s,t,\varepsilon_r)$, never given $n$, halts with probability one and outputs $\hat\pi$ with $\Pr\{|\hat\pi-\pi(s,t)|\le\varepsilon_r\pi(s,t)\}\ge 3/4$; and for every good algorithm $A$ in the adjacency-list query model without knowledge of $n$,
--   $$\mathbb E[\text{time of TriPPR on }(G,s,t)]\le C\,\log n\cdot\mathbb E\big[1+\#\text{queries of }A\text{ on }(G,s,t)\big].$$
--   This is the headline of the paper: no correct algorithm is faster than TriPPR on any valid instance by more than a logarithmic factor.
--
--   Differences from the source:
--   - reading: instance-optimal up to polylogarithmic factors → a factor C log n with C depending only on α and εr; reason: the combination of Theorem 4.1 (O(T* log n)) and Theorem 5.4 (Ω(T*)) that §5 states
--   - reading: good algorithm (probabilistically correct on every valid instance) → success probability ≥ 2/3 on every valid instance with the same εr; reason: the larger competitor class
--   - reading: time of a competitor → 1 + number of queries; reason: the output step counts; a pure query count makes the claim fail at s = t
--   - reading: (implicit) TriPPR terminates → explicit clause: the non-halting set has probability 0; reason: implied by the finite expected time
--   - reading: §4 tacitly assumes t is reachable from s → hypothesis 0 < π(s, t); reason: T* divides by π(s, t) and Lemma 4.3 fails at π(s, t) = 0 (finding I2)
--   - encoding: the algorithm is not given n → TriPPR is generic in the vertex type (no Fintype instance), sees the graph only through the Oracle and the vertices s, t; reason: it cannot enumerate V, probe unseen labels or learn n
--   - encoding: independent random walks; X1, X2, X3 independent; rounds independent → one tape of i.i.d. uniform [0, 1] entries (tapeLaw), read as independent streams; call γ of round i reads stream (i, γ); reason: the paper's randomness; independence by disjoint coordinates
--   - encoding: unit-cost RAM with Θ(log n)-bit words and O(log n)-bit floating point (§1.4, §3.3) → exact real arithmetic; time is the `cost` field, one unit per primitive, with the §3.3 heap bookkeeping charged at its binary-heap cost; reason: reading of §1.4; the floating-point error paragraph of §3.3 is not formalized
--   - reading: εr a constant relative error → 0 < εr < 1; reason: εr ≥ 1 makes the output 0 always correct; the paper's constant-factor estimation needs εr < 1
--   - reading: candidate set {u ∈ V \ F : threshold} ∪ (C^(ℓ−1) \ F) → only vertices with positive residue are activated; reason: finding I1: with threshold 0 the printed set contains unreached vertices, not computable without n; for a positive threshold the sets coincide
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 1, 36, Abstract; §5 ('Combining Theorems 4.1 and 5.4 proves the instance-optimality of TriPPR')

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_QueryModel

open MeasureTheory
open scoped ENNReal

namespace PPRInstOpt.UnknownN

/-- Instance-optimality of TriPPR when `n` is unknown (Abstract, p. 1; §5, p. 36): there is a
constant `C` depending only on `α` and `εr` such that on every valid instance `(G, s, t)` with `n`
vertices, `TriPPR(s, t, εr)` (never given `n`) halts with probability one, is correct within
relative error `εr` with probability at least `3/4`, and its expected running time is at most
`C log n` times the expected cost `E[1 + #queries]` of every good algorithm on that instance. -/
theorem instance_optimality (α εr : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < εr)
    (hε1 : εr < 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) (s t : V), 0 < ppr α G s t →
        tapeLaw {ω | ¬ triHalts G.oracle α εr s t ω} = 0 ∧
        (3 / 4 : ℝ≥0∞) ≤ tapeLaw {ω | triHalts G.oracle α εr s t ω ∧
          |triOutput G.oracle α εr s t ω - ppr α G s t| ≤ εr * ppr α G s t} ∧
        ∀ A : QueryAlg, IsGood A α εr →
          triExpTime α εr G s t ≤
            ENNReal.ofReal (C * Real.log (Fintype.card V)) * expCost A G s t := by sorry

end PPRInstOpt.UnknownN
