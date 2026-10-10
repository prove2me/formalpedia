-- Prove2me | Theorems.Thm_RunIntersect_Strict_MP_subset_MPLP
-- name    : RunIntersect.Strict.MP_subset_MPLP
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:33.492685+00:00
-- url     : https://prove2.me/theorems/4c8c42b5-0674-4f97-b09d-077e780a42fc
-- title:
--   p. 1014 — the standard linearization (8) is a relaxation: MP_G ⊆ MP^LP_G
-- statement:
--   Let $G=(V,E)$ be a hypergraph. The standard linearization $\mathrm{MP}^{\mathrm{LP}}_G$ of (8), obtained by replacing each multilinear equation $z_e=\prod_{v\in e}z_v$ by its convex hull over the unit hypercube, contains the multilinear polytope:
--   $$\mathrm{MP}_G\subseteq\mathrm{MP}^{\mathrm{LP}}_G .$$
--
--   Together with Proposition 1 this gives the inclusion $\mathrm{MP}_G\subseteq\mathrm{MP}^{\mathrm{RI}}_G$ for every hypergraph.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1014, (8) and the sentence before it

import Mathlib
import Definitions.Def_RunIntersect_Strict_Setting

namespace RunIntersect.Strict

/-- p. 1014: the standard linearization (8) is a relaxation of the multilinear set:
`MP_G ⊆ MP^LP_G`. -/
theorem MP_subset_MPLP {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α) :
    MP G ⊆ MPLP G := by sorry

end RunIntersect.Strict
