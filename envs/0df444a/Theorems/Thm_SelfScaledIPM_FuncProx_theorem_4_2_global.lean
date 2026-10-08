-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_theorem_4_2_global
-- name    : SelfScaledIPM.FuncProx.theorem_4_2_global
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:59.137716+00:00
-- url     : https://prove2.me/theorems/2865a62c-0a20-465c-8595-48ae103770fd
-- title:
--   Theorem 4.2 (4.16)–(4.21), p. 17 — relations between the proximity measures λ⁺_∞, λ_∞, λ₂, λ, γ_F, γ_G, γ_∞
-- statement:
--   Let $K$ be a proper cone with a $\nu$-self-scaled barrier $F$, and let $x\in\operatorname{int}K$, $s\in\operatorname{int}K^*$. With all measures evaluated at $(x,s)$:
--   $$\lambda^+_\infty\le\lambda_\infty\le\lambda_2\le\nu^{1/2}\lambda_\infty, \tag{4.16}$$
--   $$\gamma_F\le\nu\ln\Big(1+\frac1\nu\gamma_G\Big)\le\gamma_G, \tag{4.17}$$
--   $$\frac{\gamma_\infty^2}{1+\gamma_\infty}\le\gamma_G\le\nu\gamma_\infty, \tag{4.18}$$
--   $$\lambda_2-\ln(1+\lambda_2)\le\gamma_F, \tag{4.19}$$
--   $$\lambda\le\lambda_2, \tag{4.20}$$
--   $$\gamma_G\le\lambda_2^2(1+\gamma_\infty). \tag{4.21}$$
--
--   These inequalities let every algorithm of the paper switch between the global measures $\gamma_F,\gamma_G,\gamma_\infty$ and the local ones $\lambda_2,\lambda_\infty$; (4.19) is what turns $\gamma_F\le\beta$ into $\lambda_2\le\kappa$ in Theorem 7.1.
--
--   **Formalization Note** This item is the first part of Theorem 4.2; the part under the hypothesis $\lambda_\infty<1$ is a separate item.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 17, Theorem 4.2, (4.16)–(4.21)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Theorem 4.2** (p. 17), inequalities (4.16)–(4.21). For `x ∈ int K`, `s ∈ int K*`:
(4.16) `λ⁺_∞ ≤ λ_∞ ≤ λ₂ ≤ ν^{1/2} λ_∞`;
(4.17) `γ_F ≤ ν ln(1 + γ_G/ν) ≤ γ_G`;
(4.18) `γ_∞²/(1 + γ_∞) ≤ γ_G ≤ ν γ_∞`;
(4.19) `λ₂ − ln(1 + λ₂) ≤ γ_F`;
(4.20) `λ ≤ λ₂`;
(4.21) `γ_G ≤ λ₂² (1 + γ_∞)`; all measures at `(x, s)`. -/
theorem theorem_4_2_global
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    (x s : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    (lambdaPlusInf K F ν x s ≤ SelfScaledIPM.ShortStep.lambdaInf K F ν x s ∧
      SelfScaledIPM.ShortStep.lambdaInf K F ν x s ≤ lambda2 F ν x s ∧
      lambda2 F ν x s ≤ Real.sqrt ν * SelfScaledIPM.ShortStep.lambdaInf K F ν x s) ∧
    (gammaF K F ν x s ≤ ν * Real.log (1 + gammaG K F ν x s / ν) ∧
      ν * Real.log (1 + gammaG K F ν x s / ν) ≤ gammaG K F ν x s) ∧
    (gammaInf K F ν x s ^ 2 / (1 + gammaInf K F ν x s) ≤ gammaG K F ν x s ∧
      gammaG K F ν x s ≤ ν * gammaInf K F ν x s) ∧
    lambda2 F ν x s - Real.log (1 + lambda2 F ν x s) ≤ gammaF K F ν x s ∧
    lambdaProx F ν x s ≤ lambda2 F ν x s ∧
    gammaG K F ν x s ≤ lambda2 F ν x s ^ 2 * (1 + gammaInf K F ν x s) := by sorry

end SelfScaledIPM.FuncProx
