-- Prove2me | Theorems.Thm_PPRInstOpt_UnknownN_theorem_5_4
-- name    : PPRInstOpt.UnknownN.theorem_5_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:15:54.874736+00:00
-- url     : https://prove2.me/theorems/c143703d-d6e4-47f8-a179-891be118a298
-- title:
--   Theorem 5.4 — every good algorithm spends Ω(T*) time when n is unknown
-- statement:
--   There is a constant $c>0$ depending only on $\alpha$ and $\varepsilon_r$ such that on every valid instance $(G,s,t)$ with $\pi(s,t)>0$, every good algorithm $A$ in the adjacency-list query model without knowledge of $n$ satisfies
--   $$\mathbb E\big[1+\#\text{queries of }A\text{ on }(G,s,t)\big]\ge c\,T^*.$$
--
--   Differences from the source:
--   - reading: good algorithm (probabilistically correct on every valid instance) → success probability ≥ 2/3 on every valid instance with the same εr; reason: the convention of Theorems 6.1 and 7.1; the larger class makes the lower bound stronger
--   - reading: time of a query algorithm → 1 + number of queries; reason: the output step counts; with a pure query count the statement fails at s = t (BRIEF pitfall)
--   - encoding: n unknown, vertex labels, no Jump → discovery names; queries only on named vertices; reason: the algorithm learns exactly what the paper's model reveals
--   - encoding: Ω(T*) → ∃ c > 0 depending only on α and εr; reason: explicit constant
--   - reading: §4 tacitly assumes t is reachable from s → hypothesis 0 < π(s, t); reason: T* divides by π(s, t) and Lemma 4.3 fails at π(s, t) = 0 (finding I2)
--   - encoding: independent random walks; X1, X2, X3 independent; rounds independent → one tape of i.i.d. uniform [0, 1] entries (tapeLaw), read as independent streams; call γ of round i reads stream (i, γ); reason: the paper's randomness; independence by disjoint coordinates
--   - reading: εr a constant relative error → 0 < εr < 1; reason: εr ≥ 1 makes the output 0 always correct; the paper's constant-factor estimation needs εr < 1
--   - encoding: π(u, v) = probability that the α-discounted walk from u terminates at v → ppr α G u v = Σ_k α(1−α)^k P^k(u, v); reason: the paper's own equivalent form (p. 3); same values
--   - encoding: directed simple graph with every out-degree ≥ 1 and fixed adjacency lists → Digraph V over an arbitrary vertex type: duplicate-free out- and in-lists describing one edge set, no self-loops, nonempty out-lists; reason: same instances; list order fixes out(v, i) and in(v, i)
-- source:
--   Bertram, Jensen, Thorup, Wang, Yan, Instance-Optimality of Single-Pair Personalized PageRank, STOC 2027 submission (manuscript sha256 e1dc6b7d…), p. 33, Theorem 5.4

import Mathlib
import Definitions.Def_PPRInstOpt_UnknownN_QueryModel

open MeasureTheory
open scoped ENNReal

namespace PPRInstOpt.UnknownN

/-- Theorem 5.4 (p. 33): when `n` is unknown, every good algorithm spends `Ω(T*)` time on every
graph: there is `c > 0` depending only on `α` and `εr` such that on every valid instance every good
algorithm `A` has `E[1 + #queries] ≥ c T*`. -/
theorem theorem_5_4 (α εr : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε0 : 0 < εr) (hε1 : εr < 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : Digraph V) (s t : V), 0 < ppr α G s t →
        ∀ A : QueryAlg, IsGood A α εr →
          ENNReal.ofReal (c * Tstar α G s t) ≤ expCost A G s t := by sorry

end PPRInstOpt.UnknownN
