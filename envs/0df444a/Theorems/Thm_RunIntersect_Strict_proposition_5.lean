-- Prove2me | Theorems.Thm_RunIntersect_Strict_proposition_5
-- name    : RunIntersect.Strict.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:36.772777+00:00
-- url     : https://prove2.me/theorems/834e8c15-605f-4e5a-9901-534a7c30b204
-- title:
--   Proposition 5, p. 1019 — if G is not β-acyclic, then MP_G ⊂ MP^RI_G
-- statement:
--   Let $G=(V,E)$ be a hypergraph (finite, without loops or parallel edges). If $G$ is not β-acyclic, that is, if $G$ contains a β-cycle, then the multilinear polytope is strictly contained in the running intersection relaxation:
--   $$\mathrm{MP}_G\subsetneq\mathrm{MP}^{\mathrm{RI}}_G .$$
--
--   Equivalently, β-acyclicity is a necessary condition for the running intersection relaxation to describe the multilinear polytope exactly. Example 2 of the paper shows it is not sufficient; the sufficient condition proved in the paper is kite-free β-acyclicity (Theorem 3).
--
--   **Formalization Note** The paper's $\subset$ is strict and is encoded as Lean's `⊂` on sets ($\subseteq$ and $\neq$). $\mathrm{MP}^{\mathrm{RI}}_G$ contains every running intersection inequality (every center, neighbor set, ordering and choice of nodes $u_k$), so no inequality is missing that would make strictness easier. No hypothesis is added: if $G$ has an isolated node $v$, strictness also holds because (8) does not bound $z_v$ from below.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1019, Proposition 5

import Mathlib
import Definitions.Def_RunIntersect_Strict_Setting

namespace RunIntersect.Strict

/-- Proposition 5, p. 1019: if `G` is not β-acyclic, then `MP_G ⊂ MP^RI_G` (strict inclusion). -/
theorem proposition_5 {α : Type*} [Fintype α] [DecidableEq α] (G : Hypergraph α)
    (h : ¬ IsBetaAcyclic G) :
    MP G ⊂ MPRI G := by sorry

end RunIntersect.Strict
