-- Prove2me | Theorems.Thm_SwitchbackExp_Design_theorem_1
-- name    : SwitchbackExp.Design.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:33.566026+00:00
-- url     : https://prove2.me/theorems/16bef251-2a6a-44b2-9704-01451495d8a6
-- title:
--   Theorem 1, p. 12 — every minimax-optimal regular design flips fair coins: q₀ = q₁ = … = q_K = 1/2
-- statement:
--   Let $B>0$ and $m<T$. Under Assumptions 1–3 with bound $B$, every regular switchback design $(\mathbb T,\mathbb Q)$ that solves the minimax problem
--   $$\min_{\mathbb T\subseteq[T],\,\mathbb Q\in(0,1)^{K+1}}\ \max_{\mathbb Y\in\mathcal Y}\ r(\eta_{\mathbb T,\mathbb Q},\mathbb Y)\qquad(6)$$
--   satisfies
--   $$q_0=q_1=\dots=q_K=\tfrac12 .$$
--
--   Theorem 1 lets the design problem be restricted to fair coins, leaving only the choice of the randomization points.
--
--   **Formalization Note** Minimax optimality is the $\forall\exists$ predicate of the Setting file: the design is regular and its worst-case risk is at most that of every regular design. The statement is not vacuous: the goal theorem of the mission (Theorem 2) asserts that minimax-optimal designs exist when $m=0$ or $T=nm$ with $n\ge4$.
-- source:
--   Bojinov, Simchi-Levi, Zhao, Design and Analysis of Switchback Experiments, arXiv:2009.00148v4 (Management Science 69(7), 2023), Theorem 1, p. 12; proof EC.3.4.1, p. ec9

import Mathlib
import Definitions.Def_SwitchbackExp_Design_Model
import Definitions.Def_SwitchbackExp_Design_Setting

namespace SwitchbackExp.Design

/-- Theorem 1 (p. 12): under Assumptions 1–3, every minimax-optimal regular design flips fair coins. -/
theorem theorem_1 (m T : ℕ) (hmT : m < T) (B : ℝ) (hB : 0 < B) :
    ∀ (P : Finset ℕ) (q : ℕ → ℝ), IsMinimaxOptimal m T B P q → ∀ t ∈ P, q t = 1 / 2 := by sorry

end SwitchbackExp.Design
