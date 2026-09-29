-- Prove2me | Theorems.Thm_ResourceScheduling_Poly_p2_min_makespan_matching
-- name    : ResourceScheduling.Poly.p2_min_makespan_matching
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:33:15.828491+00:00
-- url     : https://prove2.me/theorems/a8fcfa3f-dbba-4ff4-8683-f171b7cd93b8
-- title:
--   Proof of Theorem 1 — the minimum C_max is n − |S|
-- statement:
--   Consider $P2\mid res{\cdot}{\cdot}{\cdot},\,p_j=1\mid C_{\max}$: two identical machines (speed $1$), $n$ unit-time jobs, $l$ resources with positive integer sizes $s_h$ and nonnegative integer requirements $r_{hj}\le s_h$, and no precedence constraints. Let $G$ be the graph on the jobs with an edge $\{j,k\}$ whenever $r_{hj}+r_{hk}\le s_h$ for all $h$, and let $S$ be a matching of maximum cardinality in $G$. Then the minimum value of $C_{\max}$ is
--   $$n-|S|:$$
--   some feasible schedule has $C_{\max}=n-|S|$, and every feasible schedule has $C_{\max}\ge n-|S|$.
--
--   This is the content of the proof of Theorem 1 (Garey & Johnson): "Obviously, the minimum value of $C_{\max}$ is equal to $n-|S|$." It reduces two-machine scheduling under arbitrary resource constraints to maximum matching.
--
--   **Formalization Note** The matching is a Mathlib `Subgraph` of $G$ with `IsMatching`; maximality is over all matchings of $G$, and $|S|$ is the number of its edges. The value is computed in $\mathbb R$, so there is no natural-number subtraction. The hypothesis $r_{hj}\le s_h$ is implicit in the paper. The running time $O(ln^2+n^{5/2})$ is not formalized.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 15, proof of Theorem 1 (statement p. 13)

import Mathlib
import Definitions.Def_ResourceScheduling_Poly_Model
import Definitions.Def_ResourceScheduling_Poly_CompatibilityGraph

namespace ResourceScheduling.Poly

/-- Proof of Theorem 1 (p. 15): for `P2 | res···, p_j = 1 | C_max` with every job fitting alone,
if `S` is a matching of maximum cardinality in the compatibility graph `G`, the minimum value of
`C_max` over feasible schedules is `n - |S|`: it is attained, and no feasible schedule does
better. -/
theorem p2_min_makespan_matching (I : Instance) (hm : I.m = 2) (hq : ∀ i, I.q i = 1)
    (hprec : I.NoPrecedence) (hfit : I.EveryJobFits)
    (S : I.compatGraph.Subgraph) (hS : S.IsMatching)
    (hmax : ∀ S' : I.compatGraph.Subgraph, S'.IsMatching → S'.edgeSet.ncard ≤ S.edgeSet.ncard) :
    (∃ σ : Schedule I, σ.Feasible ∧ σ.makespan = (I.n : ℝ) - S.edgeSet.ncard) ∧
      ∀ σ : Schedule I, σ.Feasible → (I.n : ℝ) - S.edgeSet.ncard ≤ σ.makespan := by sorry

end ResourceScheduling.Poly
