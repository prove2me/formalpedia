-- Prove2me | Theorems.Thm_PESContracts_Linear_linear_best_response
-- name    : PESContracts.Linear.linear_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:18.706696+00:00
-- url     : https://prove2.me/theorems/c662e4c8-ba75-4906-9474-aec2bd4ff485
-- title:
--   §4, p. 9 — best response to a linear conservation price
-- statement:
--   Let the initial forest area $a_0$ and cost curvature $h$ be positive, and let the type interval lie in $[0,1]$. At any nonnegative per-unit price $p$ and any type $\theta\in[0,1]$, the agent maximizes $p a-c_h(a-\theta a_0)$ over $a\in[0,a_0]$ by choosing
--
--   $$
--   a_L(\theta;p)=\min\{\theta a_0+p/h,a_0\}.
--   $$
--
--   For $p>0$, this maximizer is unique. The result identifies the actual action induced by a linear contract and establishes that a best response exists in Theorem 1.
--
--   **Formalization Note** The statement uses the cost function's zero-cost branch below the baseline. The paper writes the quadratic branch in its maximization display; the maximizer lies at or above the baseline. The theorem includes every $\theta\in[0,1]$, hence every supported type.
-- source:
--   Li, Ashlagi & Lo, Simple and Approximately Optimal Contracts for Payment for Ecosystem Services, SSRN preprint 3754041 (version of 2021-05-19), p. 9, §4, paragraph beginning 'The agent's best response'; https://ssrn.com/abstract=3754041

import Mathlib
import Definitions.Def_PESContracts_Linear_Model

namespace PESContracts.Linear

/-- §4, p. 9: closed-form linear best response; uniqueness for positive prices. -/
theorem linear_best_response (M : Params) (hM : M.Standing)
    (p : ℝ) (hp : 0 ≤ p) (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) :
    linAction M p θ ∈ Set.Icc 0 M.a0 ∧
    (∀ a ∈ Set.Icc 0 M.a0,
      linUtil M p θ a ≤ linUtil M p θ (linAction M p θ)) ∧
    (0 < p → ∀ a ∈ Set.Icc 0 M.a0,
      linUtil M p θ (linAction M p θ) ≤ linUtil M p θ a →
      a = linAction M p θ) := by sorry

end PESContracts.Linear
