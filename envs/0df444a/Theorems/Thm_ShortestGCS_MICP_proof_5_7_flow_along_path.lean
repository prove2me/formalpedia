-- Prove2me | Theorems.Thm_ShortestGCS_MICP_proof_5_7_flow_along_path
-- name    : ShortestGCS.MICP.proof_5_7_flow_along_path
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:26.188833+00:00
-- url     : https://prove2.me/theorems/6a8f2c6c-bd02-454d-8907-1e5f8c1fa103
-- title:
--   Proof of Theorem 5.7, p. 10 — along the path, flow conservation (5.5d) reads z′_e = z_f for consecutive edges e, f
-- statement:
--   Let $G$ be a graph of convex sets satisfying the standing assumptions of §2, let $(y, z, z')$ be feasible for the MICP (5.5), and let $p = (v_0, \dots, v_K)$ be an $s$-$t$ path all of whose edges carry flow $y_e = 1$. If $e = (v_k, v_{k+1})$ and $f = (v_{k+1}, v_{k+2})$ are consecutive edges of $p$, then
--
--   $$
--   z'_e = z_f.
--   $$
--
--   Hence the vectors $z_e, z'_e$ along the path define consistent vertex positions $x_{v_k}$, which is how an optimal solution of (2.1) is read off from one of (5.5).
--
--   **Formalization Note** The path is not assumed to be the whole support of $y$; the conclusion holds for any $s$-$t$ path with unit flow on its edges.
-- source:
--   Marcucci, Umenberger, Parrilo & Tedrake, Shortest Paths in Graphs of Convex Sets, arXiv:2101.11565v5, proof of Theorem 5.7, p. 10, seventh sentence

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun
import Definitions.Def_ShortestGCS_MICP_Setting

namespace ShortestGCS.MICP

/-- Proof of Theorem 5.7, arXiv:2101.11565v5, p. 10: for a feasible point of the MICP (5.5) and an
`s`-`t` path `p = (v_0, …, v_K)` whose edges all carry flow `1`, if `e = (v_k, v_{k+1})` and
`f = (v_{k+1}, v_{k+2})` are consecutive edges of `p`, the flow conservation (5.5d) reads `z'_e = z_f`. -/
theorem proof_5_7_flow_along_path {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n)
    (hG : IsGCS G) (y : V × V → ℝ) (z z' : V × V → Fin n → ℝ) (hfeas : IsMICPFeasible G y z z')
    (p : List V) (hp : IsPath G p) (hpy : ∀ e ∈ pathEdges p, y e = 1) :
    ∀ (k : ℕ) (hk : k + 2 < p.length),
      z' (p[k]'(by omega), p[k + 1]'(by omega)) = z (p[k + 1]'(by omega), p[k + 2]'hk) := by sorry

end ShortestGCS.MICP
