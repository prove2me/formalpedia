-- Prove2me | Theorems.Thm_PESContracts_Linear_pointwise_dominance
-- name    : PESContracts.Linear.pointwise_dominance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:10:29.190013+00:00
-- url     : https://prove2.me/theorems/db5a04e6-30f9-4f87-b58b-11e96effcd2a
-- title:
--   Appendix A.4, pp. 25–26 — pointwise doubled-linear-payoff bound
-- statement:
--   For $a_0,h,k>0$, any type $\theta\in[0,1]$, and any conservation action $a\in[0,a_0]$, the rent-free surplus is at most twice the principal's payoff from the linear price $k/2$ at that type:
--
--   $$
--   k a-c_h(a-\theta a_0)
--   \leq 2\bigl(k-k/2\bigr)
--     \min\{\theta a_0+k/(2h),a_0\}.
--   $$
--
--   This typewise comparison supplies the distribution-free inequality needed for Theorem 1.
--
--   **Formalization Note** Appendix A.4 compares the paper's optimal allocation with the linear action. The stated bound holds for every feasible action and therefore includes that allocation. Weak inequality includes boundary types and prices where equality occurs.
-- source:
--   Li, Ashlagi & Lo, Simple and Approximately Optimal Contracts for Payment for Ecosystem Services, SSRN preprint 3754041 (version of 2021-05-19), pp. 25–26, Appendix A.4, cases (i)–(vi) and closing paragraph; https://ssrn.com/abstract=3754041

import Mathlib
import Definitions.Def_PESContracts_Linear_Model

namespace PESContracts.Linear

/-- Appendix A.4, pp. 25–26: doubled linear payoff bounds rent-free surplus. -/
theorem pointwise_dominance (M : Params) (hM : M.Standing) (k : ℝ) (hk : 0 < k)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) (a : ℝ) (ha : a ∈ Set.Icc 0 M.a0) :
    k * a - cost M.h (a - θ * M.a0) ≤
      2 * ((k - k / 2) * linAction M (k / 2) θ) := by sorry

end PESContracts.Linear
