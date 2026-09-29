-- Prove2me | Theorems.Thm_SPOBounds_StronglyConvex_dual_norm_ball_max
-- name    : SPOBounds.StronglyConvex.dual_norm_ball_max
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T18:36:52.155126+00:00
-- url     : https://prove2.me/theorems/88c75451-74fc-4f5d-8400-f2a3d5ed2e0c
-- title:
--   Maximum of a linear functional over a ball: $\max_{\tilde w\in B(\hat w,r)}c^\top\tilde w = c^\top\hat w + r\|c\|_*$
-- statement:
--   Let $E$ be a finite-dimensional real normed space with dual norm $\|\cdot\|_*$, let $c$ be a continuous linear functional on $E$, let $\hat w\in E$ and let $r\ge0$. Then the maximum of $c^\top\tilde w$ over the closed ball $B(\hat w,r)=\{\tilde w:\|\tilde w-\hat w\|\le r\}$ is attained and equals
--   $$\max_{\tilde w\in B(\hat w,r)} c^\top\tilde w \;=\; c^\top\hat w + r\,\|c\|_*.$$
--
--   This is the identity used in the proof of Proposition 1 (Appendix D.1) to turn the inclusion of a ball in $S$ into an inequality involving the dual norm.
--
--   **Formalization Note** "Maximum" is stated as `IsGreatest` of the image of the closed ball: the value is attained and is an upper bound. The radius $r\ge0$ is a hypothesis; in the paper it is $r(\lambda)=(\bar\mu/2)\lambda(1-\lambda)\|w-\bar w\|^2\ge0$. Finite dimensionality guarantees that the maximum is attained.
-- source:
--   El Balghiti, Elmachtoub, Grigas, Tewari, Generalization Bounds in the Predict-then-Optimize Framework, arXiv:1905.11488v3, p. 35, Appendix D.1 (proof of Proposition 1), second display

import Mathlib

namespace SPOBounds.StronglyConvex

/-- App. D.1, p. 35, second display: the maximum of `cᵀw̃` over the closed ball
`B(ŵ, r)` is `cᵀŵ + r ‖c‖_*`. -/
theorem dual_norm_ball_max {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (c : StrongDual ℝ E) (what : E) {r : ℝ} (hr : 0 ≤ r) :
    IsGreatest ((fun v => c v) '' Metric.closedBall what r) (c what + r * ‖c‖) := by sorry

end SPOBounds.StronglyConvex
