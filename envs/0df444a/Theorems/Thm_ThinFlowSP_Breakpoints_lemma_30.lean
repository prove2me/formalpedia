-- Prove2me | Theorems.Thm_ThinFlowSP_Breakpoints_lemma_30
-- name    : ThinFlowSP.Breakpoints.lemma_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:29:38.387405+00:00
-- url     : https://prove2.me/theorems/4bce3391-7f5a-4d1a-8b92-2baf08384471
-- title:
--   Lemma 30, p. 19 — parallel composition: n ≤ n₁ + n₂ + 1 breakpoints
-- statement:
--   Let $G'_1$ and $G'_2$ be two-terminal directed acyclic multigraphs and $G' = G'_1 \parallel G'_2$ their parallel composition (sources glued, sinks glued). Let $A^* \subseteq A'$ be resetting arcs and $\nu \in \mathbb R^{A'}_{>0}$ capacities on $G'$; each part $G'_i$ carries $A^* \cap A'_i$ and the restriction of $\nu$. If $\varrho^{G'}$, $\varrho^{G'_1}$, $\varrho^{G'_2}$ are the label functions of $G'$, $G'_1$, $G'_2$ and $n, n_1, n_2$ their numbers of breakpoints, then
--   $$n \le n_1 + n_2 + 1 .$$
--
--   This is the parallel step of the structural induction proving Theorem 31.
--
--   **Formalization Note** As for Lemma 29: breakpoints of the whole label vector, counted with `Set.encard`; $A^*$ and $\nu$ restricted to the parts; any function with the defining property of $\varrho^{G'}$.
-- source:
--   Kaiser, Computation of Dynamic Equilibria in Series-Parallel Networks, arXiv:2002.11428v2, p. 19, Lemma 30

import Mathlib
import Definitions.Def_ThinFlowSP_Breakpoints_Model

namespace ThinFlowSP.Breakpoints

theorem lemma_30 (G₁ G₂ : Net) (h₁ : IsTwoTerminalDAG G₁) (h₂ : IsTwoTerminalDAG G₂)
    (Astar : Finset (G₁.A ⊕ G₂.A)) (ν : G₁.A ⊕ G₂.A → ℝ) (hν : ∀ a, 0 < ν a)
    (ρ : ℝ → (G₁.par G₂).V → ℝ) (ρ₁ : ℝ → G₁.V → ℝ) (ρ₂ : ℝ → G₂.V → ℝ)
    (hρ : IsLabelFunction (G₁.par G₂) Astar ν ρ)
    (hρ₁ : IsLabelFunction G₁ Astar.toLeft (fun a => ν (Sum.inl a)) ρ₁)
    (hρ₂ : IsLabelFunction G₂ Astar.toRight (fun a => ν (Sum.inr a)) ρ₂) :
    (breakpoints ρ).encard ≤ (breakpoints ρ₁).encard + (breakpoints ρ₂).encard + 1 := by sorry

end ThinFlowSP.Breakpoints
