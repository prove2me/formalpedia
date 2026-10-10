-- Prove2me | Theorems.Thm_ShortestGCS_MICP_proof_5_7_persp_simplify
-- name    : ShortestGCS.MICP.proof_5_7_persp_simplify
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:48.423608+00:00
-- url     : https://prove2.me/theorems/422036a6-eae7-40e3-9c79-c4fd6c7621d0
-- title:
--   Proof of Theorem 5.7, p. 10 — (5.5e) gives z_e = z′_e = 0 and cost 0 when y_e = 0, and z_e ∈ 𝒳_u, z′_e ∈ 𝒳_v, cost ℓ_e(z_e, z′_e) when y_e = 1
-- statement:
--   Let $G$ be a graph of convex sets satisfying the standing assumptions of §2, and $e = (u,v) \in \mathcal E$. Suppose $(z_e, y_e) \in \tilde{\mathcal X}_u$ and $(z'_e, y_e) \in \tilde{\mathcal X}_v$ (constraint (5.5e)). Then
--
--   1. if $y_e = 0$: $z_e = z'_e = 0$ and $\tilde\ell_e(z_e, z'_e, y_e) = 0$;
--   2. if $y_e = 1$: $z_e \in \mathcal X_u$, $z'_e \in \mathcal X_v$ and $\tilde\ell_e(z_e, z'_e, y_e) = \ell_e(z_e, z'_e)$.
--
--   Together with the path-and-cycles decomposition, this reduces the MICP cost of a binary solution to the length of a path plus the (nonnegative) lengths of cycles.
-- source:
--   Marcucci, Umenberger, Parrilo & Tedrake, Shortest Paths in Graphs of Convex Sets, arXiv:2101.11565v5, proof of Theorem 5.7, p. 10, fourth and sixth sentences

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun
import Definitions.Def_ShortestGCS_MICP_Setting

namespace ShortestGCS.MICP

/-- Proof of Theorem 5.7, arXiv:2101.11565v5, p. 10: for an edge `e = (u, v)` with flow `y_e = 0`,
constraint (5.5e) simplifies to `z_e = z'_e = 0` and the cost addend is `ℓ̃_e(0, 0, 0) = 0`; with flow
`y_e = 1`, (5.5e) becomes `z_e ∈ 𝒳_u`, `z'_e ∈ 𝒳_v` and the cost addend is
`ℓ̃_e(z_e, z'_e, 1) = ℓ_e(z_e, z'_e)`. -/
theorem proof_5_7_persp_simplify {V : Type*} {n : ℕ} (G : GCS V n)
    (hG : IsGCS G) (y : V × V → ℝ) (z z' : V × V → Fin n → ℝ) (e : V × V) (he : e ∈ G.E)
    (h55e : (z e, y e) ∈ perspectiveSet (G.X e.1) ∧ (z' e, y e) ∈ perspectiveSet (G.X e.2)) :
    (y e = 0 → z e = 0 ∧ z' e = 0 ∧ perspectiveFun (G.ℓ e) (z e, z' e) (y e) = 0) ∧
      (y e = 1 → z e ∈ G.X e.1 ∧ z' e ∈ G.X e.2 ∧
        perspectiveFun (G.ℓ e) (z e, z' e) (y e) = G.ℓ e (z e, z' e)) := by sorry

end ShortestGCS.MICP
