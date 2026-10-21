-- Prove2me | Theorems.Thm_RelationalReciprocity_Dynamics_kkt_monotone
-- name    : RelationalReciprocity.Dynamics.kkt_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:23.842163+00:00
-- url     : https://prove2.me/theorems/f7150325-09bb-4a43-a183-b76c081260c3
-- title:
--   Proof of Proposition 1, p. 43 — ∂w/∂λ > 0 and ∂e*/∂λ < 0 on the positive-wage branch
-- statement:
--   Let $\theta>0$, $\eta>0$ and the standing assumptions hold, and let $\lambda\ge0$ satisfy $\eta^2\theta^3(1+\lambda)>1$. Write
--   $$
--   w(\lambda)=\frac{(\eta^2\theta^3(1+\lambda)-1)^2}{4\eta^3\theta^3(1+\lambda)^2},\qquad e(\lambda)=\frac{1+\eta^2\theta^3(1+\lambda)}{2\eta\theta(1+\lambda)}
--   $$
--   for the wage and effort at the KKT point with (DE) multiplier $\lambda$. Then
--   $$
--   \frac{\partial w}{\partial\lambda}=\frac{\eta^2\theta^3(1+\lambda)-1}{2\eta^3\theta^3(1+\lambda)^3}>0,\qquad \frac{\partial e}{\partial\lambda}=\frac{-1}{2\eta\theta(1+\lambda)^2}<0 .
--   $$
--
--   A tighter enforcement constraint (a larger multiplier) thus raises the wage and lowers effort.
-- source:
--   Fahn, Reciprocity in Dynamic Employment Relationships, CRC TRR 190 Discussion Paper No. 198 (Nov. 8, 2019), p. 43 (PDF 45), proof of Proposition 1

import Mathlib
import Definitions.Def_RelationalReciprocity_Dynamics_Model

namespace RelationalReciprocity.Dynamics

/-- Proof of Proposition 1, p. 43: on the positive-wage branch the KKT wage increases and the KKT
effort decreases in the (DE) multiplier `λ`, with
`∂w/∂λ = (η²θ³(1+λ) − 1)/(2η³θ³(1+λ)³) > 0` and `∂e*/∂λ = −1/(2ηθ(1+λ)²) < 0`. -/
theorem kkt_monotone (P : Params) (hP : P.Standing) (hη : 0 < P.η) (lam : ℝ) (hlam : 0 ≤ lam)
    (hpos : 1 < P.η ^ 2 * P.θ ^ 3 * (1 + lam)) :
    HasDerivAt (kktWage P)
      ((P.η ^ 2 * P.θ ^ 3 * (1 + lam) - 1) / (2 * P.η ^ 3 * P.θ ^ 3 * (1 + lam) ^ 3)) lam ∧
    0 < (P.η ^ 2 * P.θ ^ 3 * (1 + lam) - 1) / (2 * P.η ^ 3 * P.θ ^ 3 * (1 + lam) ^ 3) ∧
    HasDerivAt (kktEffort P) (-1 / (2 * P.η * P.θ * (1 + lam) ^ 2)) lam ∧
    -1 / (2 * P.η * P.θ * (1 + lam) ^ 2) < 0 := by sorry

end RelationalReciprocity.Dynamics
