-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_theorem_3_8
-- name    : SelfScaledIPM.FuncProx.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:44.817135+00:00
-- url     : https://prove2.me/theorems/9ababe69-ab3a-4da0-9134-357a9712496e
-- title:
--   Theorem 3.8, pp. 10–11 — ‖F‴(x)[p₁,p₂]‖_x ≤ 2|p₁|_x‖p₂‖_x and ‖(F″(x − p₁) − F″(x))p₂‖_x ≤ (2 − σ)/(1 − σ)²‖p₁‖_x|p₂|_x
-- statement:
--   Let $K$ be a proper cone with a $\nu$-self-scaled barrier $F$, and let $x\in\operatorname{int}K$. For all $p_1,p_2\in E$,
--   $$\|F'''(x)[p_1,p_2]\|_x\le 2\,|p_1|_x\,\|p_2\|_x. \tag{3.14}$$
--   Moreover, if $v=x-p_1\in\operatorname{int}K$, then, writing $\sigma=\sigma_x(p_1)$,
--   $$\|(F''(v)-F''(x))p_2\|_x\le\frac{2-\sigma}{(1-\sigma)^2}\,\|p_1\|_x\,|p_2|_x. \tag{3.15}$$
--   The left-hand sides are vectors of $E^*$, so their norms are the dual local norms at $x$.
--
--   This is the third-derivative estimate that distinguishes self-scaled barriers from general self-concordant ones: one factor $\|p_1\|_x$ is replaced by the smaller $|p_1|_x$.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), pp. 10–11, Theorem 3.8, (3.14)–(3.15)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Theorem 3.8** (pp. 10–11). For `x ∈ int K` and `p₁, p₂ ∈ E`:
(3.14) `‖F'''(x)[p₁, p₂]‖_x ≤ 2 |p₁|_x ‖p₂‖_x` (the left side is the dual local norm of a vector of
`E*`); and if `v = x − p₁ ∈ int K`, then
(3.15) `‖(F''(v) − F''(x))p₂‖_x ≤ (2 − σ_x(p₁))/(1 − σ_x(p₁))² · ‖p₁‖_x · |p₂|_x`. -/
theorem theorem_3_8
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) :
    (∀ p₁ p₂ : EuclideanSpace ℝ (Fin n),
      SelfScaledIPM.ShortStep.dnorm F x (third F x p₁ p₂) ≤ 2 * SelfScaledIPM.ShortStep.absn K x p₁ * SelfScaledIPM.ShortStep.lnorm F x p₂) ∧
    (∀ p₁ p₂ : EuclideanSpace ℝ (Fin n), x - p₁ ∈ interior K →
      SelfScaledIPM.ShortStep.dnorm F x ((SelfScaledIPM.ShortStep.hess F (x - p₁) - SelfScaledIPM.ShortStep.hess F x) p₂) ≤
        (2 - SelfScaledIPM.ShortStep.sigma K x p₁) / (1 - SelfScaledIPM.ShortStep.sigma K x p₁) ^ 2 * SelfScaledIPM.ShortStep.lnorm F x p₁ * SelfScaledIPM.ShortStep.absn K x p₂) := by sorry

end SelfScaledIPM.FuncProx
