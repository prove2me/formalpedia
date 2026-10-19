-- Prove2me | Theorems.Thm_PDSmooth_Framework_strongConvex_Qrho
-- name    : PDSmooth.Framework.strongConvex_Qrho
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:39.439957+00:00
-- url     : https://prove2.me/theorems/e72501fc-63e2-498f-b65a-fc897b2b9349
-- title:
--   Proof of Lemma 4.2, p. 15 — Q^λ_ρ(·;x) = q_ρ + λ⁻¹D_ω(·,x) is (λ⁻¹ − γ)-strongly convex on X
-- statement:
--   Under the standing assumptions of problem (1.1), let $0<\lambda<\gamma^{-1}$, $\rho\ge0$ and $x\in\mathcal X$. Then the smoothed Bregman proximal objective
--
--   $$
--   Q^\lambda_\rho(x';x)=q_\rho(x')+\lambda^{-1}D_{\omega_{\mathcal X}}(x',x),\qquad q_\rho=f_\rho+r,
--   $$
--
--   is $(\lambda^{-1}-\gamma)$-strongly convex in $x'$ on $\mathcal X$.
--
--   This is the subproblem that Step 2 of Algorithm 1 solves approximately; its strong convexity converts the $\eta$-accuracy of Step 2 into a distance bound to $\mathrm{prox}(q_\rho,x_k,\lambda)$.
--
--   **Formalization Note** The paper uses this fact at $x=x_K$ in the proof of Lemma 4.2; it is stated here for every $x\in\mathcal X$, as the paper uses the same property for $Q^\lambda$ on p. 13. The paper takes $\rho>0$; $\rho\ge0$ also covers Lean's value $\rho=0$ when $R_{\mathcal Y}(\omega_{\mathcal Y})=0$.
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 15, proof of Lemma 4.2

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting

namespace PDSmooth.Framework

/-- Proof of Lemma 4.2, p. 15: for `0 < λ < γ⁻¹`, `ρ ≥ 0` and `x ∈ X`, the function
`Q^λ_ρ(·; x) = q_ρ + λ⁻¹ D_{ω_X}(·, x)` is `(λ⁻¹ − γ)`-strongly convex on `X`. -/
theorem strongConvex_Qrho {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam ρ : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < γ⁻¹) (hρ : 0 ≤ ρ) (x : E) (hx : x ∈ X) :
    StrongConvexOn X (lam⁻¹ - γ) (Qprox (qSmooth Φ g r ωY Y ρ) ωX lam x) := by sorry
end PDSmooth.Framework
