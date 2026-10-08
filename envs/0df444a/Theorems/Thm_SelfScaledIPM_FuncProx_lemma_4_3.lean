-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_lemma_4_3
-- name    : SelfScaledIPM.FuncProx.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:05.807402+00:00
-- url     : https://prove2.me/theorems/8dd88719-7651-41e7-a4f9-a581d3d2c24e
-- title:
--   Lemma 4.3, p. 20 — ‖v‖²_x ≤ (1 + γ_∞)/µ · ‖v‖²_w and ‖u‖²_s ≤ (1 + γ_∞)/µ · ‖u‖²_w
-- statement:
--   Let $K$ be a proper cone with a $\nu$-self-scaled barrier $F$, let $x\in\operatorname{int}K$, $s\in\operatorname{int}K^*$, and let $w\in\operatorname{int}K$ satisfy $F''(w)x=s$. Then for every $v\in E$ and $u\in E^*$,
--   $$\|v\|_x^2\le\frac{1}{\mu(x,s)}[1+\gamma_\infty(x,s)]\,\|v\|_w^2,\qquad \|u\|_s^2\le\frac{1}{\mu(x,s)}[1+\gamma_\infty(x,s)]\,\|u\|_w^2 .$$
--   Here $\|u\|_s$ is the local norm of $F_*$ at $s$ and $\|u\|_w$ the dual local norm of $F$ at $w$.
--
--   The lemma compares the local metrics at $x$ and $s$ with the scaling metric at $w$; it gives (5.14) and (5.23).
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 20, Lemma 4.3

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting
import Definitions.Def_SelfScaledIPM_FuncProx_Measures

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Lemma 4.3** (p. 20). For `x ∈ int K`, `s ∈ int K*` with scaling point `w`, every `v ∈ E` and
`u ∈ E*`: `‖v‖²_x ≤ (1/µ)(1 + γ_∞) ‖v‖²_w` and `‖u‖²_s ≤ (1/µ)(1 + γ_∞) ‖u‖²_w`, where `µ = µ(x, s)`,
`γ_∞ = γ_∞(x, s)`, `‖u‖_s` is the local norm of `F*` at `s` and `‖u‖_w` the dual local norm of `F`
at `w`. -/
theorem lemma_4_3
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    (x s w : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (hs : s ∈ interior (ConvexOptimization.dualCone K))
    (hw : SelfScaledIPM.ShortStep.IsScalingPoint K F x s w) :
    (∀ v : EuclideanSpace ℝ (Fin n),
      SelfScaledIPM.ShortStep.lnorm F x v ^ 2 ≤ (1 + gammaInf K F ν x s) / SelfScaledIPM.ShortStep.mu ν x s * SelfScaledIPM.ShortStep.lnorm F w v ^ 2) ∧
    (∀ u : EuclideanSpace ℝ (Fin n),
      SelfScaledIPM.ShortStep.lnorm (SelfScaledIPM.ShortStep.conj K F) s u ^ 2 ≤ (1 + gammaInf K F ν x s) / SelfScaledIPM.ShortStep.mu ν x s * SelfScaledIPM.ShortStep.dnorm F w u ^ 2) := by sorry

end SelfScaledIPM.FuncProx
