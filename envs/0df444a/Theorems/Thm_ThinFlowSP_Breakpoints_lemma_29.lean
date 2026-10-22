-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_lemma_29
-- name    : ThinFlowSP.Breakpoints.lemma_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:57.48058+00:00
-- url     : https://prove2.me/theorems/c3988318-6a4c-4103-a8a2-e1ed1908d10f
-- title:
--   Lemma 29, p. 19 — series composition: n ≤ n₁ + n₂ breakpoints
-- statement:
--   Let $G'_1$ and $G'_2$ be two-terminal directed acyclic multigraphs and $G' = G'_1 * G'_2$ their series composition (the sink of $G'_1$ glued to the source of $G'_2$). Let $A^* \subseteq A'$ be resetting arcs and $\nu \in \mathbb R^{A'}_{>0}$ capacities on $G'$; each part $G'_i$ carries $A^* \cap A'_i$ and the restriction of $\nu$. If $\varrho^{G'}$, $\varrho^{G'_1}$, $\varrho^{G'_2}$ are the label functions of $G'$, $G'_1$, $G'_2$ and $n, n_1, n_2$ their numbers of breakpoints, then
--   $$n \le n_1 + n_2 .$$
--
--   This is the series step of the structural induction proving Theorem 31.
--
--   **Formalization Note** Numbers of breakpoints are counted with `Set.encard` in $\mathbb N\cup\{\infty\}$, so the statement is meaningful before finiteness is known. The page's "$G'_i := G'[V_i]$" with $A^*$ left implicit is rendered by building $G'$ from the parts and restricting $A^*$ and $\nu$ to each part. A label function is any function with the defining property of $\varrho^{G'}$ (label 1 at $s$); by Corollary 15 it agrees with $\varrho^{G'}$ on $[0,\infty)$, and breakpoints only see $(0,\infty)$.
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 19, Lemma 29

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace ThinFlowSP.Breakpoints

theorem lemma_29 (G₁ G₂ : Net) (h₁ : IsTwoTerminalDAG G₁) (h₂ : IsTwoTerminalDAG G₂)
    (Astar : Finset (G₁.A ⊕ G₂.A)) (ν : G₁.A ⊕ G₂.A → ℝ) (hν : ∀ a, 0 < ν a)
    (ρ : ℝ → (G₁.series G₂).V → ℝ) (ρ₁ : ℝ → G₁.V → ℝ) (ρ₂ : ℝ → G₂.V → ℝ)
    (hρ : IsLabelFunction (G₁.series G₂) Astar ν ρ)
    (hρ₁ : IsLabelFunction G₁ Astar.toLeft (fun a => ν (Sum.inl a)) ρ₁)
    (hρ₂ : IsLabelFunction G₂ Astar.toRight (fun a => ν (Sum.inr a)) ρ₂) :
    (breakpoints ρ).encard ≤ (breakpoints ρ₁).encard + (breakpoints ρ₂).encard := by sorry

end ThinFlowSP.Breakpoints
