-- Prove2me | Theorems.Thm_SchedComplexity_NoWait_theorem_2d_equiv
-- name    : SchedComplexity.NoWait.theorem_2d_equiv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:17:44.400247+00:00
-- url     : https://prove2.me/theorems/5359cc3c-7651-4184-92a7-a11458ca683a
-- title:
--   Theorem 2(d) — G' has a Hamilton circuit iff the split graph G has a Hamilton path
-- statement:
--   Let $G'=(V',A')$ be a directed graph and $v'\in V'$. Construct $G=(V,A)$ with a new vertex $v''$:
--   $$V=V'\cup\{v''\},\qquad A=\{(u,v)\mid(u,v)\in A',\ v\ne v'\}\cup\{(u,v'')\mid(u,v')\in A'\}.$$
--   Then $G'$ has a Hamilton circuit if and only if $G$ has a Hamilton path.
--
--   This is the correctness of the reduction DIRECTED HAMILTON CIRCUIT $\propto$ DIRECTED HAMILTON PATH, which establishes the NP-completeness of the source problem of Theorem 5 from Karp's result for Hamilton circuits.
--
--   **Formalization Note** $V'=\{0,\dots,n-1\}$ and $v''$ is the new vertex $n$. A one-vertex $G'$ has a Hamilton circuit iff it has a loop at $v'$; correspondingly $G$ then has the arc $(v',v'')$. The NP-completeness of DIRECTED HAMILTON CIRCUIT (Karp) is not formalized.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 14, proof of Theorem 2(d)

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_DirectedGraphs
import Definitions.Def_SchedComplexity_NoWait_Construction

namespace SchedComplexity.NoWait

/-- Theorem 2(d), the equivalence (p. 14): for a directed graph `G'` on `Fin n` and a chosen
vertex `v'`, `G'` has a Hamilton circuit iff the graph `G` obtained by keeping the arcs of `G'`
that do not enter `v'` and redirecting the arcs entering `v'` to a new vertex `v''` has a
Hamilton path. -/
theorem theorem_2d_equiv {n : ℕ} (adj' : Fin n → Fin n → Bool) (v' : Fin n) :
    HasHamiltonCircuit adj' ↔ HasHamiltonPath (hcToHpGraph adj' v') := by sorry

end SchedComplexity.NoWait
