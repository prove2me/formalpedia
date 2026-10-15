-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC1_lemma_EC_2
-- name    : SuspensionContract.HighCostC1.lemma_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:55.030817+00:00
-- url     : https://prove2.me/theorems/8b27b76e-8ea5-497e-b533-00f89e5aa093
-- title:
--   Lemma EC.2, p. ec23 — the delay ODE (25)–(26) has a unique C¹ solution V_w̃ for every w̃ ∈ [0, w̄)
-- statement:
--   Assume the standing assumptions of the model. For every $\tilde w\in[0,\bar w)$ there is a function $V$, continuously differentiable on $[0,\tilde w]$, that solves the delay differential equation
--
--   $$(\mu+r)V(w)-\mu V\big((w+\beta)\wedge\tilde w\big)+\rho(\bar w-w)V'(w)-(\mu R-c)+(\rho-r)w=0,\qquad w\in[0,\tilde w],$$
--
--   with boundary condition $V(w)=\bar V(\tilde w)$ for all $w\ge\tilde w$; and any two such solutions agree on $\mathbb R_+$.
--
--   This justifies speaking of *the* solution $V_{\tilde w}$, on which the working-state value function is built.
--
--   **Formalization Note** A solution is only constrained on $\mathbb R_+$, so uniqueness is stated on $\mathbb R_+$. The derivative in the equation is taken within $[0,\tilde w]$ (one-sided at the endpoints), matching the class $C^1([0,\tilde w])$.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript, p. ec23, Lemma EC.2 (first sentence)

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC1_DelayODE

namespace SuspensionContract.HighCostC1
theorem lemma_EC_2 (P : Params) (hP : P.Standing) (wt : ℝ) (h0 : 0 ≤ wt) (h1 : wt < P.wbar) :
    (∃ V, P.SolvesDDE wt V) ∧
      ∀ V₁ V₂, P.SolvesDDE wt V₁ → P.SolvesDDE wt V₂ → Set.EqOn V₁ V₂ (Set.Ici 0) := by sorry
end SuspensionContract.HighCostC1
