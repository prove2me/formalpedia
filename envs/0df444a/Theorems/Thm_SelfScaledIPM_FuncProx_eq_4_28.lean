-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_eq_4_28
-- name    : SelfScaledIPM.FuncProx.eq_4_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:11.275698+00:00
-- url     : https://prove2.me/theorems/f68f2b2e-4757-4851-b74e-cec6ec3a438a
-- title:
--   (4.28), p. 19 — γ_G(x, s) ≥ ¾γ_∞(x, s) − ¼ (outer inequality)
-- statement:
--   Let $K$ be a proper cone with a $\nu$-self-scaled barrier $F$, and let $x\in\operatorname{int}K$, $s\in\operatorname{int}K^*$. Then
--   $$\gamma_G(x,s)\ge\tfrac34\gamma_\infty(x,s)-\tfrac14 .$$
--
--   In the paper this is written as a chain through $\tfrac34\mu(x,s)\sigma_x(w)^2-1=\tfrac34\mu(x,s)\sigma_x(-F_*'(s))-1$ (equal by Lemma 3.4), giving a short proof of a result of [NT97]. It is used in the proof of Theorem 7.1 to show that every corrector step from outside $\mathcal F(\beta)$ makes a uniform amount of progress.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 19, (4.28)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **(4.28)** (§4, p. 19), the outer inequality: for `x ∈ int K`, `s ∈ int K*`,
`γ_G(x, s) ≥ ¾ γ_∞(x, s) − ¼`. -/
theorem eq_4_28
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    (x s : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    (3 / 4 : ℝ) * gammaInf K F ν x s - 1 / 4 ≤ gammaG K F ν x s := by sorry

end SelfScaledIPM.FuncProx
