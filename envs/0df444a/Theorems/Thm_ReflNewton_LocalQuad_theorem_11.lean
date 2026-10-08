-- Prove2me | Theorems.Thm_ReflNewton_LocalQuad_theorem_11
-- name    : ReflNewton.LocalQuad.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:56:20.324194+00:00
-- url     : https://prove2.me/theorems/4d03d7f3-a9ec-4ddd-b4aa-6f23325bede8
-- title:
--   Theorem 11: quadratic convergence for a finite family of Newton maps
-- statement:
--   Let $\mathcal V=\{F_\nu:\mathbb R^m\to\mathbb R^m\}$ be a finite family of continuously differentiable functions on an open convex set $\mathcal C$. Suppose $x_*\in\mathcal C$, every $F_\nu(x_*)=0$, every Jacobian $\nabla F_\nu(x_*)$ is nonsingular, and for a common constant $\kappa_0$,
--
--   $$
--   \|\nabla F_\nu(x)-\nabla F_\nu(x_*)\|\le\kappa_0\|x-x_*\|\quad(x\in\mathcal C).
--   $$
--
--   For a sequence $x_{k+1}=x_k+s_k$, suppose that whenever $x_k$ is sufficiently close to $x_*$ there is a Newton solution $s^N_{\nu_k}$ for one member of the family such that $\|s_k-s^N_{\nu_k}\|\le c_1\|x_k-x_*\|^2$. Then there are a common radius $r>0$ and rate constant $C$ such that every run beginning in $B(x_*,r)$ remains there, satisfies $\|x_{k+1}-x_*\|\le C\|x_k-x_*\|^2$ at every step, and converges to $x_*$.
--
--   This abstract result transfers a uniform Newton approximation bound to local quadratic convergence.
--
--   **Formalization Note** The printed theorem uses a plus sign in $\|s_k+s^N_{\nu_k}\|$; the proof uses the difference and the plus-sign version is false. The statement uses the difference. The Newton step is specified by its linear equation. The family index may be empty, in which case there is no run to which the universal conclusion applies.
-- source:
--   Coleman & Li, On the convergence of interior-reflective Newton methods for nonlinear minimization subject to bounds, Math. Programming 67 (1994), pp. 211–212, Theorem 11 and (6.5)

import Mathlib

namespace ReflNewton.LocalQuad

/-- Theorem 11; the step error uses the difference required by the printed proof. -/
theorem theorem_11 {m : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (𝒞 : Set (EuclideanSpace ℝ (Fin m))) (h𝒞 : IsOpen 𝒞) (hconv : Convex ℝ 𝒞)
    (xstar : EuclideanSpace ℝ (Fin m)) (hx : xstar ∈ 𝒞)
    (hC1 : ∀ ν, ContDiffOn ℝ 1 (F ν) 𝒞)
    (hzero : ∀ ν, F ν xstar = 0)
    (hreg : ∀ ν, Function.Bijective (fderiv ℝ (F ν) xstar))
    (κ₀ : ℝ)
    (hκ : ∀ ν, ∀ x ∈ 𝒞,
      ‖fderiv ℝ (F ν) x - fderiv ℝ (F ν) xstar‖ ≤ κ₀ * ‖x - xstar‖)
    (c₁ : ℝ) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball xstar r ⊆ 𝒞 ∧
      ∃ C : ℝ, ∀ (x s : ℕ → EuclideanSpace ℝ (Fin m)) (ν : ℕ → ι),
        x 0 ∈ Metric.ball xstar r →
        (∀ k, x (k + 1) = x k + s k) →
        (∀ k, x k ∈ Metric.ball xstar r →
          ∃ sN : EuclideanSpace ℝ (Fin m),
            fderiv ℝ (F (ν k)) (x k) sN = -F (ν k) (x k) ∧
            ‖s k - sN‖ ≤ c₁ * ‖x k - xstar‖ ^ 2) →
        (∀ k, x k ∈ Metric.ball xstar r ∧
          ‖x (k + 1) - xstar‖ ≤ C * ‖x k - xstar‖ ^ 2) ∧
        Filter.Tendsto x Filter.atTop (nhds xstar) := by sorry

end ReflNewton.LocalQuad
