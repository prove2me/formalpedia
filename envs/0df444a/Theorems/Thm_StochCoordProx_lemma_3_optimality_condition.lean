-- Prove2me | Theorems.Thm_StochCoordProx_lemma_3_optimality_condition
-- name    : StochCoordProx.lemma_3_optimality_condition
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:33:47.15267+00:00
-- url     : https://prove2.me/theorems/a462ad8a-3ae6-41c9-9b32-9fd4f9756e3c
-- title:
--   Lemma 3 — optimality condition for a composite problem
-- statement:
--   Consider the composite problem $\min_{x\in\operatorname{dom}\phi}\theta(x)+\phi(x)$ on $\mathbb R^m$, where $\theta$ is differentiable and $\phi$ is convex on its convex domain $D=\operatorname{dom}\phi$. Let $y^*\in D$. Then $y^*$ is a stationary point of $\theta+\phi$ on $D$ if and only if
--
--   $$
--   \langle\nabla\theta(y^*),y-y^*\rangle+\phi(y)-\phi(y^*)\ge0\qquad\forall y\in D .
--   $$
--
--   Here "stationary" means directional stationarity: for every $y\in D$, $\liminf_{t\downarrow0}[(\theta+\phi)(y^*+t(y-y^*))-(\theta+\phi)(y^*)]/t\ge0$.
--
--   The lemma is applied to the subproblem (9) when $\psi$ is convex along the subspaces, with $\theta$ the quadratic part and $\phi(d)=\psi(x_k+U_kd)$.
--
--   Differences from the source:
--   - reading: y* is a stationary point (undefined in the paper, cited from [32]) → IsDirStationary: liminf_{t↓0} ((θ+φ)(y*+t(y−y*)) − (θ+φ)(y*))/t ≥ 0 for every y ∈ D; reason: first-order stationarity on a convex set; reading it as (15) or as −∇θ(y*) ∈ ∂φ(y*) would make the lemma a restatement
--   - encoding: φ convex on its convex domain dom φ; y* in the problem's domain → φ : ℝᵐ → ℝ with ConvexOn ℝ D φ (which includes convexity of D), and y* ∈ D; reason: only the values of φ on D enter the statement
--   - encoding: an unspecified finite-dimensional space (ℝᵖ in the application) → EuclideanSpace ℝ (Fin m), for every m; reason: Lean convention; same instances
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, Lemma 3, display (15), p.9

import Mathlib
import Definitions.Def_StochCoordProx_IsDirStationary

open scoped InnerProductSpace

namespace StochCoordProx

/-- **Lemma 3 (optimality condition for a composite problem).** Consider
`min_{x ∈ dom φ} θ(x) + φ(x)` on `ℝᵐ`, where `θ` is differentiable and `φ` is convex on the convex
domain `dom φ = D`. Then `y* ∈ D` is a stationary point if and only if
`⟨∇θ(y*), y − y*⟩ + φ(y) − φ(y*) ≥ 0` for all `y ∈ D`  (15).

Necoara & Chorobura, arXiv:2104.13370v3, Lemma 3, display (15), p.9.

**Formalization Note.** "Stationary point", which the paper does not define, is read as
first-order directional stationarity of `θ + φ` on `D` (`IsDirStationary`). `φ` is a real
function on `ℝᵐ` and `D` plays the role of `dom φ`; `ConvexOn ℝ D φ` includes convexity of `D`.
`ℝᵐ` is `EuclideanSpace ℝ (Fin m)` and `∇θ` is `gradient θ`. -/
theorem lemma_3_optimality_condition {m : ℕ} (θ φ : EuclideanSpace ℝ (Fin m) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin m))) (hθ : Differentiable ℝ θ) (hφ : ConvexOn ℝ D φ)
    (ystar : EuclideanSpace ℝ (Fin m)) (hystar : ystar ∈ D) :
    IsDirStationary (fun y => θ y + φ y) D ystar ↔
      ∀ y ∈ D, ⟪gradient θ ystar, y - ystar⟫_ℝ + φ y - φ ystar ≥ 0 := by sorry

end StochCoordProx
