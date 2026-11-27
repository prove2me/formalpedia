-- Prove2me | Theorems.Thm_SPFacilityGraph_sp_onto_gate
-- name    : SPFacilityGraph.sp_onto_gate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-27T00:54:48.711191+00:00
-- url     : https://prove2.me/theorems/6fb11011-ed99-46b0-a8bf-e785784f6730
-- title:
--   Option sets of SP onto mechanisms are gated
-- statement:
--   Let $G\subseteq\mathbb R^k$ be a straight-edge metric graph with graph distance $d_G$, let $n\ge 2$, and let $M:G^n\to G$ be a deterministic mechanism that is strategyproof and onto. Fix an agent $i$ and the reports $\boldsymbol x_{-i}$ of the others, and write $f(y)=M(y,\boldsymbol x_{-i})$ for agent $i$'s outcome when reporting $y$. Then for all $y,z\in G$,
--
--   $$
--   d_G\big(y,f(z)\big)=d_G\big(y,f(y)\big)+d_G\big(f(y),f(z)\big).
--   $$
--
--   In words, agent $i$'s option set $O=\{f(z):z\in G\}$ is **gated**: the outcome $f(y)$ obtained by reporting the true location $y$ lies on a shortest path from $y$ to every other attainable outcome. This is the metric form of the Schummer–Vohra description of option sets: an interval on a segment, a subtree on a tree, and on graphs with cycles the cycles neighborhood plus attached subtrees for the cycle dictator (a single point for the others). It implies that $f$ is $1$-Lipschitz, the property used to build deterministic PL attributions (Lemma Q.4).
--
--   **Formalization Note** $(y,\boldsymbol x_{-i})$ is `Function.update x i y`; strategyproofness is `IsSP` and onto is `Function.Surjective M`.
-- source:
--   Schummer–Vohra, Strategy-proof location on a network, J. Econ. Theory 104 (2002) 405–428, Theorems 1, 3 and 4 (option sets of strategy-proof onto rules); used in Rogowski–Dziubiński, arXiv:2611.05092, proof of Lemma Q.4, pp.51–52

import Mathlib
import Definitions.Def_SPFacilityGraph_IsSP

set_option autoImplicit false

namespace SPFacilityGraph

theorem sp_onto_gate {k n : ℕ} (hn : 2 ≤ n) (G : MetricGraph k) (M : Profile G n → G.Pt)
    (hSP : IsSP G M) (hM : Function.Surjective M) (x : Profile G n) (i : Fin n) (y z : G.Pt) :
    G.dist y (M (Function.update x i z)) =
      G.dist y (M (Function.update x i y)) +
        G.dist (M (Function.update x i y)) (M (Function.update x i z)) := by sorry

end SPFacilityGraph
