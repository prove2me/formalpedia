-- Prove2me | Theorems.Thm_RunIntersect_Tight_proposition_1
-- name    : RunIntersect.Tight.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:35:25.369376+00:00
-- url     : https://prove2.me/theorems/d1ce52b9-5f29-47c2-94ee-97bd953d290a
-- title:
--   Proposition 1, p. 1012 — running intersection inequalities are valid for MP_G
-- statement:
--   Let $G=(V,E)$ be a hypergraph and $\mathrm{MP}_G$ its multilinear polytope. Every running intersection inequality (5) of $G$ — for any center $e_0$, any neighbors $e_k$, $k\in K$, adjacent to $e_0$ with $\tilde E=\{e_0\cap e_k\}$ having the running intersection property, any running intersection ordering of $\tilde E$ and any choice of nodes $u_k\in N(e_0\cap e_k)$ — holds on $\mathrm{MP}_G$:
--   $$-\sum_{k\in K:\,N(e_0\cap e_k)\neq\emptyset} z_{u_k}+\sum_{v\in e_0\setminus\bigcup_{k}e_k} z_v+\sum_{k\in K}z_{e_k}-z_{e_0}\le \omega-1\qquad\forall z\in\mathrm{MP}_G.$$
--
--   Together with the validity of the standard linearization (8), this gives $\mathrm{MP}_G\subseteq\mathrm{MP}^{\mathrm{RI}}_G$, one half of Theorem 3.
--
--   **Formalization Note** No acyclicity is assumed, as on the page. The inequality data range over the structure `RIData G` (see the Setting file).
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1012, Proposition 1

import Mathlib
import Definitions.Def_RunIntersect_Tight_Setting

namespace RunIntersect.Tight

theorem proposition_1 {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α) :
    ∀ d : RIData G, ∀ z ∈ MP G, d.lhs z ≤ d.rhs := by sorry

end RunIntersect.Tight
