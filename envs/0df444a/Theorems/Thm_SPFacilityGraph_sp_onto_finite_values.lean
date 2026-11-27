-- Prove2me | Theorems.Thm_SPFacilityGraph_sp_onto_finite_values
-- name    : SPFacilityGraph.sp_onto_finite_values
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T00:01:09.969815+00:00
-- url     : https://prove2.me/theorems/a2e4d2d2-79c7-5a07-bc84-c0e2f94fcc76
-- title:
--   SP onto mechanisms take finitely many non-report values
-- statement:
--   Let $G\subseteq\mathbb R^k$ be a straight-edge metric graph, let $n\ge 2$, and let $M:G^n\to G$ be a deterministic mechanism that is strategyproof and onto. Then there is a finite set $W\subseteq G$ such that every outcome is either one of the reports or a point of $W$: for every profile $\boldsymbol x\in G^n$,
--
--   $$
--   M(\boldsymbol x)\in\{x_1,\dots,x_n\}\cup W .
--   $$
--
--   On a segment, $W$ can be taken to be the set of the $2^n$ thresholds $t_S$ of the generalized median voter scheme; on general graphs the Schummer–Vohra characterization adds the graph vertices (projections of reports onto paths or attached trees are reports or vertices). Together with the Lipschitz property of each report, this finiteness is what makes the mechanism agree with a single selector of $\Pi(W)$ on each simplex of a suitable triangulation (Lemma Q.4).
--
--   **Formalization Note** Strategyproofness is `IsSP` (2.2) and onto is `Function.Surjective M`.
-- source:
--   Schummer–Vohra, Strategy-proof location on a network, J. Econ. Theory 104 (2002) 405–428, Theorems 1 and 4 (with Proposition 1 on intervals); used in Rogowski–Dziubiński, arXiv:2611.05092, proof of Lemma Q.4, pp.51–52 ((Q.3)–(Q.6))

import Mathlib
import Definitions.Def_SPFacilityGraph_IsSP

set_option autoImplicit false

namespace SPFacilityGraph

theorem sp_onto_finite_values {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k) (M : Profile G n → G.Pt)
    (hSP : IsSP G M) (hM : Function.Surjective M) :
    ∃ W : Finset G.Pt, ∀ x : Profile G n, (∃ i, M x = x i) ∨ M x ∈ W := by sorry

end SPFacilityGraph
