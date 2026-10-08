-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_lemma_3_4
-- name    : SelfScaledIPM.FuncProx.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:56.139376+00:00
-- url     : https://prove2.me/theorems/b4218a08-c74b-4965-ab21-fa305a5c4f3d
-- title:
--   Lemma 3.4, p. 8 — σ_s(−F′(x)) = σ_x(−F′_*(s)) = σ_x(w)² = … and σ_s(x) = σ_x(s) = σ_w(x)² = … at the scaling point w
-- statement:
--   Let $K$ be a proper cone with a $\nu$-self-scaled barrier $F$, let $x\in\operatorname{int}K$, $s\in\operatorname{int}K^*$, and let $w\in\operatorname{int}K$ be the scaling point, $F''(w)x=s$. Then
--   $$\sigma_s(-F'(x))=\sigma_x(-F_*'(s))=\sigma_x(w)^2=\sigma_w(-F'(x))^2=\sigma_s(-F'(w))^2=\sigma_w(-F_*'(s))^2,$$
--   $$\sigma_s(x)=\sigma_x(s)=\sigma_w(x)^2=\sigma_x(-F'(w))^2=\sigma_w(s)^2=\sigma_s(w)^2.$$
--   Here each $\sigma_v(u)$ is the σ-measure of the measures file, determined by the space of $u$ and of $v$.
--
--   The lemma says the scaling point is a "geometric mean" of $x$ and $s$ in the σ-sense; it is used to identify the quantity $1+\gamma_\infty$ with $\mu\,\sigma_x(w)^2$ and $1+\lambda^+_\infty$ with $\sigma_w(x)^2/\mu$.
--
--   **Formalization Note** Each chain is stated as consecutive equalities. Translating the twelve σ's: $\sigma_s(-F'(x))$ is `sigma K* s (-F'(x))`, $\sigma_x(-F_*'(s))$ is `sigma K x (-F_*'(s))`, $\sigma_w(-F'(x))$ is `sigma K* (-F'(w)) (-F'(x))`, $\sigma_s(x)$ is `sigma K (-F_*'(s)) x`, $\sigma_x(s)$ is `sigma K* (-F'(x)) s`, and so on, as in the docstring of `sigma`.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 8, Lemma 3.4

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Lemma 3.4** (p. 8). For `x ∈ int K`, `s ∈ int K*` and their scaling point `w`
(`F''(w)x = s`):
`σ_s(−F'(x)) = σ_x(−F*'(s)) = σ_x(w)² = σ_w(−F'(x))² = σ_s(−F'(w))² = σ_w(−F*'(s))²` and
`σ_s(x) = σ_x(s) = σ_w(x)² = σ_x(−F'(w))² = σ_w(s)² = σ_s(w)²`, each `σ` translated by the space of
its argument and the cone of its centre (see `sigma`). -/
theorem lemma_3_4
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    (x s w : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hs : s ∈ interior (ConvexOptimization.dualCone K))
    (hw : SelfScaledIPM.ShortStep.IsScalingPoint K F x s w) :
    (SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) s (-gradient F x) = SelfScaledIPM.ShortStep.sigma K x (-gradient (SelfScaledIPM.ShortStep.conj K F) s) ∧
      SelfScaledIPM.ShortStep.sigma K x (-gradient (SelfScaledIPM.ShortStep.conj K F) s) = SelfScaledIPM.ShortStep.sigma K x w ^ 2 ∧
      SelfScaledIPM.ShortStep.sigma K x w ^ 2 = SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) (-gradient F w) (-gradient F x) ^ 2 ∧
      SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) (-gradient F w) (-gradient F x) ^ 2 =
        SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) s (-gradient F w) ^ 2 ∧
      SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) s (-gradient F w) ^ 2 =
        SelfScaledIPM.ShortStep.sigma K w (-gradient (SelfScaledIPM.ShortStep.conj K F) s) ^ 2) ∧
    (SelfScaledIPM.ShortStep.sigma K (-gradient (SelfScaledIPM.ShortStep.conj K F) s) x = SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) (-gradient F x) s ∧
      SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) (-gradient F x) s = SelfScaledIPM.ShortStep.sigma K w x ^ 2 ∧
      SelfScaledIPM.ShortStep.sigma K w x ^ 2 = SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) (-gradient F x) (-gradient F w) ^ 2 ∧
      SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) (-gradient F x) (-gradient F w) ^ 2 =
        SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) (-gradient F w) s ^ 2 ∧
      SelfScaledIPM.ShortStep.sigma (ConvexOptimization.dualCone K) (-gradient F w) s ^ 2 = SelfScaledIPM.ShortStep.sigma K (-gradient (SelfScaledIPM.ShortStep.conj K F) s) w ^ 2) := by sorry

end SelfScaledIPM.FuncProx
