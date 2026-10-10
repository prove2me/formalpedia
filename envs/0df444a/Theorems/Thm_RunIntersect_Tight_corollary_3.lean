-- Prove2me | Theorems.Thm_RunIntersect_Tight_corollary_3
-- name    : RunIntersect.Tight.corollary_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:28.167982+00:00
-- url     : https://prove2.me/theorems/a493896a-9512-477f-81e5-c127d57a9c04
-- title:
--   Corollary 3, p. 1021 — for a two-laminar β-acyclic hypergraph without isolated nodes, MP_G = MP^RI_G
-- statement:
--   Let $G=(V,E)$ be a two-laminar β-acyclic hypergraph in which every node lies in some edge. Then the running intersection relaxation is exact:
--   $$\mathrm{MP}_G=\mathrm{MP}^{\mathrm{RI}}_G .$$
--
--   This is the base case of the induction proving Theorem 3, and it is used again for the piece $G_\alpha$ in the inductive step.
--
--   **Formalization Note** The hypothesis that $G$ has no isolated node is not printed in the paper but is necessary: for $V=\{a,b,c\}$, $E=\{\{a,b\}\}$ (two-laminar and β-acyclic), the point with $z_c=-1$ and all other coordinates $0$ satisfies (8) and every running intersection inequality — none of them bounds $z_c$ from below — but is not in $\mathrm{MP}_G$, where $z_c\ge 0$.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1021, Corollary 3

import Mathlib
import Definitions.Def_RunIntersect_Tight_Setting

namespace RunIntersect.Tight

theorem corollary_3 {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α) (hlam : IsLaminar G 2)
    (hβ : IsBetaAcyclic G) (hiso : NoIsolated G) :
    MP G = MPRI G := by sorry

end RunIntersect.Tight
