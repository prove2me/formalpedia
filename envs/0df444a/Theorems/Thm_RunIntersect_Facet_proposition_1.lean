-- Prove2me | Theorems.Thm_RunIntersect_Facet_proposition_1
-- name    : RunIntersect.Facet.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:41.070589+00:00
-- url     : https://prove2.me/theorems/83bf6b72-3f3d-479c-941b-cbeee1001b97
-- title:
--   Proposition 1, p. 1012 — running intersection inequalities are valid for MP_G
-- statement:
--   Let $G=(V,E)$ be a hypergraph. Every running intersection inequality for $G$, with any center $e_0$, any admissible set of neighbors $e_k$, $k\in K$, any running intersection ordering of $\tilde E$ and any choice of the nodes $u_k$, is valid for the multilinear polytope:
--   $$-\sum_{k\in K:\,N(e_0\cap e_k)\neq\emptyset} z_{u_k}+\sum_{v\in e_0\setminus\bigcup_{k}e_k} z_v+\sum_{k\in K}z_{e_k}-z_{e_0}\ \le\ \omega-1\qquad\forall z\in\mathrm{MP}_G.$$
--
--   Validity is the first half of "defines a facet" in Proposition 4.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1012, Proposition 1

import Mathlib
import Definitions.Def_RunIntersect_Facet_Setting

namespace RunIntersect.Facet

/-- Proposition 1, p. 1012. Running intersection inequalities are valid for the multilinear
polytope. -/
theorem proposition_1 {α : Type*} [Fintype α] [DecidableEq α]
    (G : Hypergraph α) (d : RIData G) :
    ∀ z ∈ MP G, d.lhs z ≤ d.rhs := by sorry

end RunIntersect.Facet
