-- Prove2me | Theorems.Thm_WeakGraphOracles_OneSided_forbidden_copy_packing
-- name    : WeakGraphOracles.OneSided.forbidden_copy_packing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:21:09.551198+00:00
-- url     : https://prove2.me/theorems/85231c68-41f1-4752-95fa-cfb103850150
-- title:
--   Lemma 4.1 — packing copies of one forbidden member
-- statement:
--   Let $F$ be a finite family of connected graphs, each with at least one and at most $k$ edges. Write $r=|F|$. If $\epsilon>0$ and $G$ requires more than $\epsilon|E(G)|$ edge deletions to become $F$-free, then some $H\in F$ has an edge-disjoint collection $C$ of appearances in $G$ satisfying
--
--   $$|C|\ge\frac{\epsilon|E(G)|}{rk}.$$
--
--   Farness at $\epsilon>0$ already forces $F$ to be nonempty, and hence $k>0$, so the denominator is positive. Here $k$ is an upper bound; family members need not have equal edge counts. The real comparison retains the exact stated bound without rounding down the integer cardinality. This identifies a single forbidden member carrying a positive packing fraction.
--
--   Differences from the source:
--   - reading: a size r collection of k-size graphs → each member has at most k edges (and is connected with at least one edge); reason: the §4.1 standing assumption on the same page reads at most k edges, and the proof of Theorem 8 applies the lemma to families of mixed sizes
--   - encoding: finite simple graphs with labels [n] → SimpleGraph (Fin n), with finite patterns carrying their own order; reason: relabeling by the standard bijection preserves every graph, appearance, degree and edge count
--   - encoding: minimum number of actual edge deletions, with strict farness → ENNReal infimum of cardinalities of feasible deletion sets; comparison with ENNReal.ofReal of epsilon times the edge or vertex count; reason: the feasible family is finite and nonempty for the stated patterns, so the infimum is its attained integer minimum; empty feasible families have value infinity, never a fabricated zero
--   - encoding: at least epsilon|E|/(rk) appearances → the same real inequality against the natural cardinality of a finite collection of labeled injective maps; reason: retains the exact lower bound and each copy labeling; edge-disjointness prevents counting several labelings of one edge image
-- source:
--   Oded Lachish, Amit Levi, Ilan Newman, Testability of General Graphs with Weak Query Oracles, STOC 2027 submission #274 (October 2026), p. 6 (PDF p. 7), Lemma 4.1 and the §4.1 standing assumptions

import Mathlib
import Definitions.Def_WeakGraphOracles_OneSided_testing

set_option autoImplicit false

namespace WeakGraphOracles.OneSided

/-- Lemma 4.1: k bounds the edge count of each pattern, rather than
being the exact edge count of all patterns. Strict farness at `ε > 0` already
forces `F` nonempty, and then admissibility forces `k > 0`. -/
theorem forbidden_copy_packing (F : Finset Pattern) (k : ℕ)
    (hF : AdmissibleFamily F k)
    {n : ℕ} (G : SimpleGraph (Fin n)) (ε : ℝ) (hε : 0 < ε)
    (hfar : EdgeFar F ε G) :
    ∃ H ∈ F, ∃ C : Finset (Appearance H G), EdgeDisjoint C ∧
      ε * (edges G).card / ((F.card : ℝ) * k) ≤ (C.card : ℝ) := by sorry

end WeakGraphOracles.OneSided
