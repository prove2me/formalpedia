-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_atar_prop_A_2
-- name    : SWSSNet.Diffusion.atar_prop_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:55.905186+00:00
-- url     : https://prove2.me/theorems/e24825fb-f646-4a52-b331-21ad2d57d497
-- title:
--   p. 17 — Atar (2005a, Prop. A.2), as quoted: on a tree, (37) has a unique solution Ψ(α, β) for every (α, β) ∈ D
-- statement:
--   Let the class–pool graph $G$ of the network be a tree. For every $\alpha\in\mathbb R^I$ and $\beta\in\mathbb R^J$ with $\langle e,\alpha\rangle=\langle e,\beta\rangle$ there is exactly one array $z=[z_{ij}]$ such that
--   $$
--   z_{ij}=0\ \ (i\not\sim j),\qquad \sum_j z_{ij}=\alpha_i\ \ \forall i,\qquad \sum_i z_{ij}=\beta_j\ \ \forall j. \qquad (37)
--   $$
--
--   This makes the map $\Psi$ of the paper well defined and linear on $D=\{(\alpha,\beta):\langle e,\alpha\rangle=\langle e,\beta\rangle\}$. The drift (42), the matrices $B_1,B_2$ and every later statement rest on it. Uniqueness is the network-flow fact that a system of flow-conservation equations supported on a spanning tree has a unique solution.
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, p. 17, (37) and Atar (2005a, Proposition A.2) as quoted

import Mathlib
import Definitions.Def_SWSSNet_Diffusion_Network

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSNet.Diffusion

/-- Atar (2005a), Proposition A.2, as quoted on p. 17: on a tree, (37) has exactly one solution for
every `(α, β) ∈ D`, i.e. with `⟨e,α⟩ = ⟨e,β⟩`. -/
theorem atar_prop_A_2 {I J : ℕ} (N : TreeNetwork I J) (α : Fin I → ℝ) (β : Fin J → ℝ)
    (hD : ∑ i, α i = ∑ j, β j) :
    ∃! z : Fin I → Fin J → ℝ, IsFlow N α β z := by sorry

end SWSSNet.Diffusion
