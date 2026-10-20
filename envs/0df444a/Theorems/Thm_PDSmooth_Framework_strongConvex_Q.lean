-- Prove2me | Theorems.Thm_PDSmooth_Framework_strongConvex_Q
-- name    : PDSmooth.Framework.strongConvex_Q
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:43.554701+00:00
-- url     : https://prove2.me/theorems/e1f3d32f-ec27-4206-b458-fcb7c50d6618
-- title:
--   §4, p. 13 — for 0 < λ < γ⁻¹ the function Q^λ(·;x) = q + λ⁻¹D_ω(·,x) is (λ⁻¹ − γ)-strongly convex on X
-- statement:
--   Under the standing assumptions of problem (1.1), let $0<\lambda<\gamma^{-1}$ and $x\in\mathcal X$. Then the Bregman proximal objective
--
--   $$
--   Q^\lambda(x';x)=q(x')+\lambda^{-1}D_{\omega_{\mathcal X}}(x',x)
--   $$
--
--   is $(\lambda^{-1}-\gamma)$-strongly convex in $x'$ on $\mathcal X$, i.e. for $x',x''\in\mathcal X$ and $a,b\ge0$ with $a+b=1$,
--
--   $$
--   Q^\lambda(ax'+bx'';x)\le a\,Q^\lambda(x';x)+b\,Q^\lambda(x'';x)-ab\,\frac{\lambda^{-1}-\gamma}{2}\|x'-x''\|^2 .
--   $$
--
--   This is what makes the proximal subproblem (2.9) well posed (its minimizer is unique) and gives quadratic growth around it, which every later estimate of the mission uses.
--
--   **Formalization Note** The paper's remark cites $\lambda^{-1}>\gamma$ and the $1$-strong convexity of $\omega_{\mathcal X}$; the result also uses the $\gamma$-weak convexity (1.4) of $\Phi(\cdot,y)$ and the convexity of $r$, both part of the standing assumptions. Strong convexity is Mathlib's zeroth-order `StrongConvexOn`.
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 13, remark after (4.2)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting

namespace PDSmooth.Framework

/-- §4, p. 13 (remark after (4.2)): for `0 < λ < γ⁻¹` and `x ∈ X`, the function
`Q^λ(·; x) = q + λ⁻¹ D_{ω_X}(·, x)` is `(λ⁻¹ − γ)`-strongly convex on `X`. -/
theorem strongConvex_Q {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < γ⁻¹) (x : E) (hx : x ∈ X) :
    StrongConvexOn X (lam⁻¹ - γ) (Qprox (qObj Φ g r Y) ωX lam x) := by sorry
end PDSmooth.Framework
