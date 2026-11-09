-- Prove2me | Theorems.Thm_StochMatchPoly_lemma_3_2
-- name    : StochMatchPoly.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:28:54.570453+00:00
-- url     : https://prove2.me/theorems/5805beb2-bd3d-4b21-a477-44b51838a2c8
-- title:
--   Lemma 3.2 — stability of the optimal covered set under changes at one vertex
-- statement:
--   Let $G=(V,E)$ be a finite simple graph, $w\in\mathbb R^V$ a generic weight vector and $S(G,w)$ the optimal covered set.
--
--   1. Let $G-i$ be obtained by deleting all edges at the vertex $i$ (keeping $i$ as an isolated vertex). Then either $S(G-i,w)=S(G,w)$, or $S(G-i,w)=S(G,w)\,\triangle\,\{i,j\}$ for some $j\ne i$; and a change is possible only if $i\in S(G,w)$.
--   2. More generally, if $(G,w)$ and $(G',w')$ differ only in edges incident to $i$ and in the weight of $i$, and both $w$ and $w'$ are generic, then
--
--   $$|S(G,w)\,\triangle\,S(G',w')|\le 2,$$
--
--   and if the two sets differ, at least one of them contains $i$.
--
--   This is the stability property that bounds the effect of resampling one vertex's randomness in the proof of (7).
--
--   Differences from the source:
--   - encoding: S(G, w), the optimal covered set of a generic w → any T with IsOptCovered G.edgeFinset w T (the covered set of some score-maximizing matching); reason: for generic w all maximizers have the same covered set (proved in the sanity file), so T is S(G, w)
--   - encoding: deleting a vertex i from G → G.deleteIncidenceSet i (i kept as an isolated vertex); reason: the proof regards both matchings on V(G) 'with i isolated in the second instance'; no instance changes
--   - encoding: a finite graph G (the setting of Lemma 3.1, §3) → a finite simple graph (SimpleGraph on a Fintype V); reason: §4.1: all graphs in the main argument are finite, undirected and simple; a matching uses no loop and parallel copies of an edge cover the same vertices, so the covered-set statements do not change
--   - encoding: (G, w) and (G′, w′) differ only in edges incident to i and in the weight of i → ∀ u v, u ≠ i → v ≠ i → (G.Adj u v ↔ G′.Adj u v), and w v = w′ v for v ≠ i; reason: Lean convention; the same pairs of instances
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), Lemma 3.2, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_StochMatchPoly_mu
import Definitions.Def_StochMatchPoly_perturbedCover

open Classical

namespace StochMatchPoly

/-- S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), Lemma 3.2 (Stability of the optimal covered set), p.5 (PDF p.6).

"Let w be generic. Deleting a vertex i from G either leaves the optimal covered set unchanged or
changes it by the symmetric difference {i, j} for some j ≠ i. A change is possible only if i is
covered in S(G, w). More generally, suppose (G, w) and (G′, w′) differ only in edges incident to i
and in the weight of i, and both weight vectors are generic. Then |S(G, w) △ S(G′, w′)| ≤ 2. If
the sets differ, at least one of them contains i."

**Formalization Note.** `S(G, w)` is any `T` with `IsOptCovered G.edgeFinset w T` (unique for
generic `w`). "Deleting a vertex i" keeps `i` as an isolated vertex, as the proof does ("with i
isolated in the second instance"): it is `G.deleteIncidenceSet i`. The two parts are the two
conjuncts; "differ only in edges incident to i" is agreement of the adjacency relations on pairs
of vertices both different from `i`. -/
theorem lemma_3_2 {V : Type*} [Fintype V] :
    (∀ (G : SimpleGraph V) (w : V → ℝ) (i : V) (T T' : Finset V), IsGeneric w →
      IsOptCovered G.edgeFinset w T → IsOptCovered (G.deleteIncidenceSet i).edgeFinset w T' →
      (T' = T ∨ ∃ j, j ≠ i ∧ T' = symmDiff T {i, j}) ∧ (T' ≠ T → i ∈ T)) ∧
    (∀ (G G' : SimpleGraph V) (w w' : V → ℝ) (i : V) (T T' : Finset V),
      (∀ u v, u ≠ i → v ≠ i → (G.Adj u v ↔ G'.Adj u v)) → (∀ v, v ≠ i → w v = w' v) →
      IsGeneric w → IsGeneric w' →
      IsOptCovered G.edgeFinset w T → IsOptCovered G'.edgeFinset w' T' →
      (symmDiff T T').card ≤ 2 ∧ (T ≠ T' → i ∈ T ∨ i ∈ T')) := by sorry

end StochMatchPoly
