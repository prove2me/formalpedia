-- Prove2me | Theorems.Thm_RunIntersect_Tight_theorem_3
-- name    : RunIntersect.Tight.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:34.833234+00:00
-- url     : https://prove2.me/theorems/8cb912eb-a462-4d30-9b30-c665358786dd
-- title:
--   Theorem 3, p. 1023 — for a kite-free β-acyclic hypergraph G without isolated nodes, MP_G = MP^RI_G
-- statement:
--   Let $G=(V,E)$ be a kite-free β-acyclic hypergraph in which every node lies in some edge. Then the running intersection relaxation of the multilinear set coincides with the multilinear polytope:
--   $$\mathrm{MP}_G=\mathrm{MP}^{\mathrm{RI}}_G .$$
--   Here $\mathrm{MP}_G$ is the convex hull of $\mathcal S_G=\{z\in\{0,1\}^{V+E}: z_e=\prod_{v\in e}z_v\}$, and $\mathrm{MP}^{\mathrm{RI}}_G$ is the standard linearization (8) together with all running intersection inequalities (5).
--
--   This is the paper's main characterization: for kite-free β-acyclic hypergraphs, the multilinear polytope is described in the original space by a family of explicit, combinatorially defined inequalities.
--
--   **Formalization Note** The hypothesis that $G$ has no isolated node is not printed in the paper but is necessary: for $V=\{a,b,c\}$, $E=\{\{a,b\}\}$ (kite-free and β-acyclic), the point with $z_c=-1$ and all other coordinates $0$ satisfies (8) and every running intersection inequality — (8) only has $z_c\le 1$ and every node of (5) lies in its center edge — but is not in $\mathrm{MP}_G$, where $z_c\ge 0$. The paper's proof treats "one maximal edge" as "$V$ is an edge", which is this hypothesis. Points are functions on `α ⊕ Finset α`, vanishing off the coordinates of $G$.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1023, Theorem 3 (proof §5.3, pp. 1035–1037)

import Mathlib
import Definitions.Def_RunIntersect_Tight_Setting

namespace RunIntersect.Tight

theorem theorem_3 {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α) (hkite : IsKiteFree G)
    (hβ : IsBetaAcyclic G) (hiso : NoIsolated G) :
    MP G = MPRI G := by sorry

end RunIntersect.Tight
