-- Prove2me | Theorems.Thm_RunIntersect_Strict_proposition_1
-- name    : RunIntersect.Strict.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:27.489477+00:00
-- url     : https://prove2.me/theorems/2ac536e1-da6c-45db-bf97-afed9c92a4da
-- title:
--   Proposition 1, p. 1012 — running intersection inequalities are valid for MP_G
-- statement:
--   Let $G=(V,E)$ be a hypergraph and consider any running intersection inequality of $G$: a center $e_0\in E$, neighbors $e_k$, $k\in K$ (distinct edges other than $e_0$, each meeting $e_0$) such that $\tilde E=\{e_0\cap e_k:k\in K\}$ has the running intersection property, a running intersection ordering of $\tilde E$ with sets $N(e_0\cap e_k)$, and nodes $u_k\in N(e_0\cap e_k)$ whenever this set is nonempty. Then every $z\in\mathrm{MP}_G$ satisfies
--   $$-\sum_{k\in K:\,N(e_0\cap e_k)\neq\emptyset}z_{u_k}+\sum_{v\in e_0\setminus\bigcup_{k\in K}e_k}z_v+\sum_{k\in K}z_{e_k}-z_{e_0}\le\omega-1,$$
--   where $\omega$ is the number of connected components of $\tilde G=(e_0,\tilde E)$.
--
--   This is the validity of the inequalities defining $\mathrm{MP}^{\mathrm{RI}}_G$, and so, with $\mathrm{MP}_G\subseteq\mathrm{MP}^{\mathrm{LP}}_G$, it yields $\mathrm{MP}_G\subseteq\mathrm{MP}^{\mathrm{RI}}_G$.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1012, Proposition 1 (inequality (5), p. 1011)

import Mathlib
import Definitions.Def_RunIntersect_Strict_Setting

namespace RunIntersect.Strict

/-- Proposition 1, p. 1012: every running intersection inequality (5) is valid for `MP_G`. -/
theorem proposition_1 {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α)
    (d : RIData G) (z : α ⊕ Finset α → ℝ) (hz : z ∈ MP G) :
    d.lhs z ≤ d.rhs := by sorry

end RunIntersect.Strict
