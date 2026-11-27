-- Prove2me | Theorems.Thm_SPFacilityGraph_sp_onto_lipschitz
-- name    : SPFacilityGraph.sp_onto_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T00:01:03.467335+00:00
-- url     : https://prove2.me/theorems/2dc59077-42d0-5487-a5ac-7490efb73bbf
-- title:
--   SP onto mechanisms are $1$-Lipschitz in each report
-- statement:
--   Let $G\subseteq\mathbb R^k$ be a straight-edge metric graph with graph distance $d_G$, let $n\ge 2$, and let $M:G^n\to G$ be a deterministic mechanism that is strategyproof and onto. Then $M$ is $1$-Lipschitz in each report: for every profile $\boldsymbol x\in G^n$, every agent $i$ and every report $y\in G$,
--
--   $$
--   d_G\big(M(y,\boldsymbol x_{-i}),\,M(\boldsymbol x)\big)\;\le\;d_G(y,x_i).
--   $$
--
--   Equivalently, for fixed reports $\boldsymbol x_{-i}$ of the others, the map $y\mapsto M(y,\boldsymbol x_{-i})$, which by strategyproofness selects a nearest point of agent $i$'s option set, is nonexpansive. This is a consequence of the Schummer–Vohra characterizations: on a segment the map is a clamp onto an interval, on a tree a nearest-point projection onto a subtree composed with projections, and on a graph with cycles it is the identity on the cycles neighborhood for the cycle dictator (or constant for the others) glued with tree mechanisms on the attached trees. It is one of the two properties used to build a deterministic PL attribution (Lemma Q.4).
--
--   **Formalization Note** Strategyproofness is `IsSP` (2.2) and onto is `Function.Surjective M`; $(y,\boldsymbol x_{-i})$ is `Function.update x i y`.
-- source:
--   Schummer–Vohra, Strategy-proof location on a network, J. Econ. Theory 104 (2002) 405–428, Theorems 1 and 4 (with Proposition 1 on intervals); used in Rogowski–Dziubiński, arXiv:2611.05092, proof of Lemma Q.4, pp.51–52 ((Q.3)–(Q.6))

import Mathlib
import Definitions.Def_SPFacilityGraph_IsSP

set_option autoImplicit false

namespace SPFacilityGraph

theorem sp_onto_lipschitz {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k) (M : Profile G n → G.Pt)
    (hSP : IsSP G M) (hM : Function.Surjective M) (x : Profile G n) (i : Fin n) (y : G.Pt) :
    G.dist (M (Function.update x i y)) (M x) ≤ G.dist y (x i) := by sorry

end SPFacilityGraph
