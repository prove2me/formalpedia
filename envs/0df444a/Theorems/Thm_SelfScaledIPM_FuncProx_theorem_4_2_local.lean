-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_theorem_4_2_local
-- name    : SelfScaledIPM.FuncProx.theorem_4_2_local
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:10.367983+00:00
-- url     : https://prove2.me/theorems/4c081f76-2198-4012-9499-1ea1fc1c46a5
-- title:
--   Theorem 4.2 (4.22)–(4.23), p. 17 — if λ_∞ < 1 then γ_∞ ≤ λ_∞/(1 − λ_∞) and γ_F ≤ γ_G ≤ λ₂²/(1 − λ_∞)
-- statement:
--   Let $K$ be a proper cone with a $\nu$-self-scaled barrier $F$, and let $x\in\operatorname{int}K$, $s\in\operatorname{int}K^*$ with $\lambda_\infty(x,s)<1$. Then, with all measures at $(x,s)$,
--   $$\gamma_\infty\le\frac{\lambda_\infty}{1-\lambda_\infty}, \tag{4.22}$$
--   $$\gamma_F\le\gamma_G\le\frac{\lambda_2^2}{1-\lambda_\infty}. \tag{4.23}$$
--
--   Near the central path the global measures are therefore controlled by the local ones; Theorem 7.1 uses (4.22) to bound $\gamma_\infty$ and $\gamma_G$ at the start of a predictor step.
--
--   **Formalization Note** This item is the second part of Theorem 4.2; (4.16)–(4.21) are a separate item.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 17, Theorem 4.2, (4.22)–(4.23)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Theorem 4.2** (p. 17), inequalities (4.22)–(4.23). For `x ∈ int K`, `s ∈ int K*` with
`λ_∞(x, s) < 1`: (4.22) `γ_∞ ≤ λ_∞/(1 − λ_∞)` and (4.23) `γ_F ≤ γ_G ≤ λ₂²/(1 − λ_∞)`. -/
theorem theorem_4_2_local
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    (x s : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hs : s ∈ interior (ConvexOptimization.dualCone K))
    (hlam : SelfScaledIPM.ShortStep.lambdaInf K F ν x s < 1) :
    gammaInf K F ν x s ≤ SelfScaledIPM.ShortStep.lambdaInf K F ν x s / (1 - SelfScaledIPM.ShortStep.lambdaInf K F ν x s) ∧
      gammaF K F ν x s ≤ gammaG K F ν x s ∧
      gammaG K F ν x s ≤ lambda2 F ν x s ^ 2 / (1 - SelfScaledIPM.ShortStep.lambdaInf K F ν x s) := by sorry

end SelfScaledIPM.FuncProx
