-- Prove2me | Theorems.Thm_TBSGStrategyIteration_value_eq_inverse_mul_cost
-- name    : TBSGStrategyIteration.value_eq_inverse_mul_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T00:41:13.941167+00:00
-- url     : https://prove2.me/theorems/ae2645d1-3755-468f-8308-16d60c122c77
-- title:
--   Lemma 3.2 — value vector as $(I - \gamma P_\pi)^{-1} c_\pi$
-- statement:
--   For every strategy profile $\pi$, the value vector (the expected total discounted cost $\sum_k \gamma^k P_\pi^k c_\pi$) is
--   $$v_\pi = (I - \gamma P_\pi)^{-1} c_\pi .$$
--   This is the linear-algebra form of the value vector used throughout the paper.
--
--   **Formalization Note.** `(1 - G.γ • π.transMat)⁻¹` is Mathlib's matrix inverse; $I - \gamma P_\pi$ is invertible (Lemma 3.1), so the junk value of the inverse of a singular matrix does not arise.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 4, Lemma 3.2

import Mathlib
import Definitions.Def_TBSGStrategyIteration_value

namespace TBSGStrategyIteration

/-- Lemma 3.2: for every strategy profile `π`, `v_π = (I − γP_π)⁻¹ c_π`. Here `v_π` is the
expected total discounted cost `∑_k γ^k P_π^k c_π` (Def. 2.5) and `⁻¹` is the matrix inverse
(`I − γP_π` is invertible, Lemma 3.1). -/
theorem value_eq_inverse_mul_cost {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (π : Profile G) :
    value G π = (1 - G.γ • π.transMat)⁻¹.mulVec π.costVec := by sorry

end TBSGStrategyIteration
