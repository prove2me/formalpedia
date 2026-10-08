-- Prove2me | Theorems.Thm_SelfScaledIPM_ShortStep_corollary_3_14
-- name    : SelfScaledIPM.ShortStep.corollary_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:52.664981+00:00
-- url     : https://prove2.me/theorems/f02ea899-8acf-44d8-b114-5f9172702bae
-- title:
--   Corollary 3.14, p. 14 — ‖[F″(w)/µ − F″(x)]v‖_x ≤ δ‖v‖_x and ‖[F∗″(t)/µ − F∗″(s)]u‖_s ≤ δ‖u‖_s
-- statement:
--   Under the hypotheses of Lemma 3.13 — $x \in \operatorname{int} K$, $s \in \operatorname{int} K^*$, $w$ the scaling point with $F''(w)x = s$, $t = -F'(w)$, $\mu > 0$ and $\delta = |s/\mu + F'(x)|_x < 1$ — for all $v \in E$ and $u \in E^*$,
--   $$\Big\|\Big[\tfrac{1}{\mu}F''(w) - F''(x)\Big]v\Big\|_x \le \delta\|v\|_x,\qquad (3.25)$$
--   $$\Big\|\Big[\tfrac{1}{\mu}F_*''(t) - F_*''(s)\Big]u\Big\|_s \le \delta\|u\|_s.\qquad (3.26)$$
--
--   This is the operator-norm form of Lemma 3.13 and is used to bound the error term in the analysis of the short step (Theorem 6.4).
--
--   **Formalization Note** In (3.25) the vector $[F''(w)/\mu - F''(x)]v$ is a dual vector, so its norm at $x$ uses the inverse Hessian (`dnorm F x`), while $\|v\|_x$ is `lnorm F x v`. In (3.26) the vector is primal and its norm at $s$ is `dnorm F* s`, while $\|u\|_s$ is `lnorm F* s u`.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 14, Corollary 3.14, (3.25)–(3.26)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.ShortStep

/-- **Corollary 3.14** (p. 14). Under the hypotheses of Lemma 3.13 (`δ = |s/µ + F'(x)|_x < 1`,
`t = −F'(w)`), for all `v ∈ E`, `u ∈ E*`:
(3.25) `‖[F''(w)/µ − F''(x)]v‖_x ≤ δ‖v‖_x` (the left vector lies in `E*`, so the dual-space norm
at `x`), and (3.26) `‖[F*''(t)/µ − F*''(s)]u‖_s ≤ δ‖u‖_s` (the left vector lies in `E`, so the
other-space norm at `s` for `F*`). -/
theorem corollary_3_14 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x s w : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) (hw : IsScalingPoint K F x s w)
    (μ : ℝ) (hμ : 0 < μ)
    (hδ : absn (ConvexOptimization.dualCone K) (-gradient F x) (μ⁻¹ • s + gradient F x) < 1) :
    let δ := absn (ConvexOptimization.dualCone K) (-gradient F x) (μ⁻¹ • s + gradient F x)
    let t := -gradient F w
    (∀ v : EuclideanSpace ℝ (Fin n),
      dnorm F x ((μ⁻¹ • hess F w - hess F x) v) ≤ δ * lnorm F x v) ∧
    (∀ u : EuclideanSpace ℝ (Fin n),
      dnorm (conj K F) s ((μ⁻¹ • hess (conj K F) t - hess (conj K F) s) u) ≤
        δ * lnorm (conj K F) s u) := by sorry

end SelfScaledIPM.ShortStep
