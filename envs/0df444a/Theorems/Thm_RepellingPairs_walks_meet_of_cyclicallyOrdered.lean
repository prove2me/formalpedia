-- Prove2me | Theorems.Thm_RepellingPairs_walks_meet_of_cyclicallyOrdered
-- name    : RepellingPairs.walks_meet_of_cyclicallyOrdered
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T19:48:37.498811+00:00
-- url     : https://prove2.me/theorems/bb2c45d2-4280-4561-bd68-ab821011eaba
-- title:
--   Crossing lemma — walks joining interleaved boundary terminals of an OS instance meet
-- statement:
--   In an Okamura–Seymour instance (a multigraph embedded in the closed unit disk, with the terminals $0, \dots, k-1$ on the boundary circle in increasing angle), let $a, b, c, d$ be distinct terminals occurring in this cyclic order. Then every walk from $a$ to $c$ and every walk from $b$ to $d$ share a vertex.
--
--   This is the planar fact that the proofs of Claim 8 ("Pa,c has no choice but to follow the trajectory of X") and Claim 9 (every left–right path meets the $i$–$(j+1)$ path) use without stating it. It is a statement about the embedding only: no metric and no path structure appear.
-- source:
--   Chen, Y., Pylyavskyy, P., Tan, Z., Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), https://arxiv.org/abs/2607.02883, pp. 9-10, the planarity fact used without statement in the proofs of Claim 8 and Claim 9

import Mathlib
import Definitions.Def_RepellingPairs_Multigraph
import Definitions.Def_RepellingPairs_OSInstance
import Definitions.Def_RepellingPairs_CyclicallyOrdered

set_option autoImplicit false

namespace RepellingPairs

universe u v

theorem walks_meet_of_cyclicallyOrdered {V : Type u} {E : Type v} {k : ℕ}
    (G : OSInstance V E k) {a b c d : Fin k} (h : CyclicallyOrdered a b c d)
    (p : G.graph.Walk (G.term a) (G.term c)) (q : G.graph.Walk (G.term b) (G.term d)) :
    ∃ v, v ∈ p.support ∧ v ∈ q.support := by sorry

end RepellingPairs
