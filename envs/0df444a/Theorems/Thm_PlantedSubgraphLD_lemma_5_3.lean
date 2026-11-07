-- Prove2me | Theorems.Thm_PlantedSubgraphLD_lemma_5_3
-- name    : PlantedSubgraphLD.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:02.403052+00:00
-- url     : https://prove2.me/theorems/506ec72c-046c-40e3-a6ea-4dee002bffaf
-- title:
--   Lemma 5.3 — subcubic edge-owned tree decompositions
-- statement:
--   Let $F$ be a finite connected graph with $\mathrm{tw}(F)\le k$. Then $F$ has a tree decomposition $(T,(B_x)_{x\in V(T)})$ of width at most $k$ together with a map $\pi:E(F)\to V(T)$ such that
--
--   1. the endpoints of every edge $e$ lie in $B_{\pi(e)}$;
--   2. each node of $T$ owns at most one edge: $|\pi^{-1}(x)|\le1$ for every node $x$;
--   3. $T$ has maximum degree at most $3$.
--
--   This normal form is the first step of the proof of Proposition 5.1: owning at most one edge per node lets the tree be cut into pieces with prescribed numbers of edges.
--
--   Differences from the source:
--   - encoding: tw(Γ), the minimum width of a tree decomposition → tw Γ := sInf {w | TreewidthLE Γ w} with the published RobertsonSeymour1986.GM5.TreewidthLE; reason: for a finite graph the set is nonempty and the infimum is attained; same value
--   - encoding: a tree decomposition (T, (Bx)) of width at most k (Definition 5.2: the nodes whose bags contain v induce a connected subtree) → RobertsonSeymour1986.GM5.IsTreeDecomposition F t B on a finite tree type T (bags on a path contain the intersection of its end bags) with |Bx| ≤ k + 1; reason: for a tree the path condition is equivalent to connectedness of each T[v]; width ≤ k is |Bx| ≤ k + 1
--   - encoding: |π⁻¹(x)| ≤ 1 and maximum degree at most 3 → Set.ncard (π ⁻¹' {x}) ≤ 1 and Set.ncard (t.neighborSet x) ≤ 3; reason: cardinalities of finite sets
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), Lemma 5.3, §5.1, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Definitions.Def_PlantedSubgraphLD_tw

namespace PlantedSubgraphLD

/-- **Lemma 5.3.** Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth*
(manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §5.1, Lemma 5.3, p.26 (PDF p.28): "For a connected graph F, if
tw(F) ≤ k, then F has a tree decomposition (T, (Bx)x∈V(T)) of width at most k together with a
map, π : E(F) → V(T), such that • the endpoints of every edge e lie in Bπ(e); • each node of T
owns at most one edge, in the sense that |π⁻¹(x)| ≤ 1; • T has maximum degree at most 3."

**Formalization Note** The tree decomposition is the published
`RobertsonSeymour1986.GM5.IsTreeDecomposition` on a finite tree type `T`; width at most `k` is
`|Bₓ| ≤ k + 1` for every node. Degrees and fibre sizes are `Set.ncard`. -/
theorem lemma_5_3 (k : ℕ) {V : Type} [Fintype V] [DecidableEq V] (F : SimpleGraph V)
    (hF : F.Connected) (htw : tw F ≤ k) :
    ∃ (T : Type) (_ : Fintype T) (t : SimpleGraph T) (B : T → Finset V) (π : F.edgeSet → T),
      RobertsonSeymour1986.GM5.IsTreeDecomposition F t B ∧ (∀ x, (B x).card ≤ k + 1) ∧
      (∀ e : F.edgeSet, ∀ v ∈ (e : Sym2 V), v ∈ B (π e)) ∧
      (∀ x, (π ⁻¹' {x}).ncard ≤ 1) ∧
      (∀ x, (t.neighborSet x).ncard ≤ 3) := by sorry

end PlantedSubgraphLD
