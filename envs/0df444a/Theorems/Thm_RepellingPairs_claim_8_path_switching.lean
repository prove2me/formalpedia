-- Prove2me | Theorems.Thm_RepellingPairs_claim_8_path_switching
-- name    : RepellingPairs.claim_8_path_switching
-- status  : Proved
-- author  : @iris
-- created : 2026-11-07T11:04:36.294314+00:00
-- url     : https://prove2.me/theorems/3f2d45a1-7776-4763-bb03-db086b15c2ea
-- title:
--   Claim 8 — switching two intersecting designated paths gives designated paths
-- statement:
--   Let $P$ be a shortest path structure of an OS instance and $a,b,c,d$ distinct terminals appearing on the boundary in this order. Suppose $P_{a,b}$ and $P_{d,c}$ intersect, and let $R=P_{a,b}\cap P_{d,c}$. Then both paths traverse $R$ in the same direction,
--
--   $$
--   P_{a,b}=P_a\cdot R\cdot P_b,\qquad P_{d,c}=Q_d\cdot R\cdot Q_c,
--   $$
--
--   and the switched paths are the designated ones:
--
--   $$
--   P_{a,c}=P_a\cdot R\cdot Q_c,\qquad P_{d,b}=Q_d\cdot R\cdot P_b.
--   $$
--
--   This is what keeps Step 1 of §3 inside the designated paths.
--
--   Differences from the source:
--   - generalization: P satisfies all repelling paths conditions (p.9) → any shortest path structure, with no metric; reason: the printed proof uses only the structure and the embedding; the statement specializes to the source's setting
--   - reading: "Assume that Pa and Qd share an endpoint, and Pb and Qc share an endpoint" in the definition of switching, and "let X, Y be paths obtained by switching" → the shared endpoints are part of the conclusion; reason: for this boundary order they are forced, so the printed assumption excludes nothing; the conclusion is stronger, not weaker
--   - encoding: G embedded in a closed disk with terminals on the boundary in a prescribed cyclic order → a topological embedding in the unit disk of ℂ, terminals Fin k at strictly increasing angles in [0, 2π); reason: every closed disk is homeomorphic to the unit disk; a mirror image changes no condition used
--   - reading: a graph ("All graphs are finite") → a finite multigraph; reason: the paper's realizations contain parallel edges (proof of Lemma 33, p.35)
--   - reading: the intersection of two paths is empty or a subpath of both → the common vertices and the common edges are exactly those of a contiguous piece of both, in either direction of the second; reason: subpaths are subgraphs of G; with parallel edges the vertex sets alone would not give a subpath
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), Claim 8, p.9; path switching, pp.8–9

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_PathStructure
import Definitions.Def_RepellingPairs_CyclicallyOrdered

set_option autoImplicit false

namespace RepellingPairs

universe u v

/-- **Claim 8.** Let `a, b, c, d` be distinct terminals on the boundary in this order, with `P a b` intersecting
`P d c`. Then `R = P a b ∩ P d c` is traversed in the same direction by both, `P a b = Pa·R·Pb` and
`P d c = Qd·R·Qc`, and the switched paths are designated: `P a c = Pa·R·Qc` and `P d b = Qd·R·Pb`.
Chen, Pylyavskyy, Tan, arXiv:2607.02883 (version of October 23, 2026), Claim 8, p.9, with path switching,
pp.8–9.

**Formalization Note.** The definition of switching assumes that `Pa`, `Qd` and `Pb`, `Qc` share endpoints; for
this boundary order it holds, and it is part of the conclusion here. -/
theorem claim_8_path_switching {V : Type u} {E : Type v} {k : ℕ} [Fintype V] [Fintype E]
    (G : OSInstance V E k) (P : PathStructure G) {a b c d : Fin k}
    (horder : CyclicallyOrdered a b c d)
    (hint : ¬ (P.path a b).1.VertexDisjoint (P.path d c).1) :
    ∃ (x y : V) (R : G.graph.Walk x y)
      (Pa : G.graph.Walk (G.term a) x) (Pb : G.graph.Walk y (G.term b))
      (Qd : G.graph.Walk (G.term d) x) (Qc : G.graph.Walk y (G.term c)),
      (P.path a b).1 = Pa.append (R.append Pb) ∧
      (P.path d c).1 = Qd.append (R.append Qc) ∧
      Multigraph.Walk.IsIntersection (P.path a b).1 (P.path d c).1 R ∧
      (P.path a c).1 = Pa.append (R.append Qc) ∧
      (P.path d b).1 = Qd.append (R.append Pb) := by sorry

end RepellingPairs
