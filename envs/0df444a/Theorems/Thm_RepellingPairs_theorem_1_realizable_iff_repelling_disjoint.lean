-- Prove2me | Theorems.Thm_RepellingPairs_theorem_1_realizable_iff_repelling_disjoint
-- name    : RepellingPairs.theorem_1_realizable_iff_repelling_disjoint
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:43.579886+00:00
-- url     : https://prove2.me/theorems/b1a029f1-be78-457d-8ddf-4bbb7319dd62
-- title:
--   Theorem 1 — a path structure is realized iff the paths of every repelling pair are disjoint
-- statement:
--   Let $D$ be a Kalmanson metric on the terminals of an Okamura-Seymour instance $(G,T)$, and let $P=\{P_{t,t'}\}$ be a shortest path structure. The following are equivalent:
--
--   1. There exist nonnegative edge lengths $\{\ell_e\}_{e\in E(G)}$ such that for every pair $t,t'$ of terminals, $P_{t,t'}$ is a shortest $t$-$t'$ path in $G$ and the length of $P_{t,t'}$ equals $D(t,t')$.
--   2. For every repelling pair $(t_1,t_2)$ and $(t_1',t_2')$, the paths $P_{t_1,t_2}$ and $P_{t_1',t_2'}$ are vertex-disjoint.
--
--   The repelling pairs include the repeated pair $(t,t)$, whose path is trivial.
--
--   This separates the realization problem into a combinatorial layer (a graph and a family of paths with prescribed intersections) and a numerical layer (the edge lengths). The paper's recognition of outerplanar metrics and its recovery of minimum OS realizations rest on it.
--
--   Differences from the source:
--   - reading: Pt,t′ is indeed the shortest t-t′ path in G → Pt,t′ is a shortest t-t′ path; reason: §3, p.7 restates it as "a shortest t–t′ path", the LP has non-strict inequalities, and shortest paths may tie
--   - encoding: Pt,t′ is shortest among t-t′ paths → Q ranges over paths, that is, walks with no repeated vertex; reason: the LP of §3, p.7 uses simple paths; for nonnegative lengths this equals the minimum over all walks
--   - encoding: G embedded in a closed disk with terminals on the boundary in a prescribed cyclic order → a topological embedding in the unit disk of ℂ, terminals Fin k at strictly increasing angles in [0, 2π); reason: every closed disk is homeomorphic to the unit disk; a mirror image changes no condition used
--   - reading: a graph ("All graphs are finite") → a finite multigraph; reason: the paper's realizations contain parallel edges (proof of Lemma 33, p.35)
--   - reading: the intersection of two paths is empty or a subpath of both → the common vertices and the common edges are exactly those of a contiguous piece of both, in either direction of the second; reason: subpaths are subgraphs of G; with parallel edges the vertex sets alone would not give a subpath
--   - encoding: a metric D on T → D : Fin k → Fin k → ℝ with zero diagonal, symmetry, positivity off the diagonal and the triangle inequality; reason: the definition of a metric on the terminal set
--   - encoding: the paths are disjoint → they share no vertex; reason: §2, p.6 states D-goodness with "vertex-disjoint"
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), Theorem 1, p.3

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_IsMetric
import Definitions.Def_RepellingPairs_IsKalmanson
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_PathLength
import Definitions.Def_RepellingPairs_Repel

set_option autoImplicit false

namespace RepellingPairs

universe u v

/-- **Theorem 1.** For a Kalmanson metric `D` on `T`, an Okamura-Seymour instance `(G, T)` and a shortest
path structure `P`, nonnegative edge lengths making every `P t t′` a shortest path of length `D t t′`
exist if and only if the paths of every repelling pair are disjoint. Chen, Pylyavskyy, Tan, Paths and
Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), Theorem 1, p.3.

**Formalization Note.** Finite multigraph; terminals `Fin k` in boundary order, the order for which `D` is
Kalmanson. Trivial pairs `(t, t)` are inside the repelling quantifier. "The shortest" means a shortest
path (§3, p.7: "a shortest t–t′ path"). -/
theorem theorem_1_realizable_iff_repelling_disjoint {V : Type u} {E : Type v} {k : ℕ}
    [Fintype V] [Fintype E] (G : OSInstance V E k) (D : Fin k → Fin k → ℝ)
    (hD : IsMetric D) (hK : IsKalmanson D) (P : PathStructure G) :
    (∃ ℓ : E → ℝ, (∀ e, 0 ≤ ℓ e) ∧ ∀ i j,
        (P.path i j).1.len ℓ = D i j ∧
        ∀ Q : G.graph.Path (G.term i) (G.term j), (P.path i j).1.len ℓ ≤ Q.1.len ℓ) ↔
    ∀ i j i' j', Repel D i j i' j' →
      (P.path i j).1.VertexDisjoint (P.path i' j').1 := by sorry

end RepellingPairs
