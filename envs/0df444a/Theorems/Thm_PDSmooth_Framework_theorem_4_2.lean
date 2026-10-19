-- Prove2me | Theorems.Thm_PDSmooth_Framework_theorem_4_2
-- name    : PDSmooth.Framework.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:46.908161+00:00
-- url     : https://prove2.me/theorems/e8e2ee31-38a2-43e2-98eb-81e652fdb797
-- title:
--   Theorem 4.2, p. 17 — for λ ∈ (0.8γ⁻¹, γ⁻¹), Algorithm 1 stops within ⌈(q(x₁) − q*)/((γλ/(1 − γλ) − 4)η)⌉ + 1 iterations
-- statement:
--   Under the standing assumptions of problem (1.1), let $\eta>0$ and $\lambda\in(0.8\gamma^{-1},\gamma^{-1})$, and let $q^*$ be a lower bound of $q$ on $\mathcal X$ (for instance the optimal value of (1.1), assumed finite). Then every run $(x_k)_{k\ge1}$ of Algorithm 1 terminates: there is a first iteration $K\ge1$ at which the stopping test (4.6) holds, and
--
--   $$
--   K\le\left\lceil\frac{q(x_1)-q^*}{\bigl(\frac{\gamma\lambda}{1-\gamma\lambda}-4\bigr)\eta}\right\rceil+1. \tag{4.26}
--   $$
--
--   The condition $\lambda>0.8\gamma^{-1}$ makes the denominator positive, so each non-terminal iteration decreases $q$ by a fixed amount.
--
--   **Formalization Note** "The optimal value $q^*>-\infty$" is encoded as any real lower bound of $q$ on $\mathcal X$; the infimum is one such bound, and a smaller bound only enlarges the right-hand side, so the statement is equivalent. The ceiling is `Int.ceil` and $K$ is compared as an integer.
-- source:
--   Zhao, A primal-dual smoothing framework for max-structured non-convex optimization, arXiv:2003.04375v5, p. 17, Theorem 4.2, (4.26)

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting

namespace PDSmooth.Framework

/-- Theorem 4.2, p. 17: for `λ ∈ (0.8γ⁻¹, γ⁻¹)`, every run of Algorithm 1 terminates, at a first
iteration `K ≥ 1` with `K ≤ ⌈(q(x₁) − q*)/((γλ/(1 − γλ) − 4)η)⌉ + 1`, where `q*` is any lower bound
of `q` on `X` (in particular the optimal value of (1.1)). -/
theorem theorem_4_2 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam η qstar : ℝ) (hlam0 : 0.8 * γ⁻¹ < lam) (hlam1 : lam < γ⁻¹) (hη : 0 < η)
    (hqstar : ∀ z ∈ X, qstar ≤ qObj Φ g r Y z)
    (x : ℕ → E) (hx : IsAlg1Run X Y Φ g r ωX ωY γ lam η x) :
    ∃ K : ℕ, 1 ≤ K ∧
      (K : ℤ) ≤ ⌈(qObj Φ g r Y (x 1) - qstar) / ((γ * lam / (1 - γ * lam) - 4) * η)⌉ + 1 ∧
      Stops γ lam η x K ∧ (∀ j : ℕ, 1 ≤ j → j < K → ¬ Stops γ lam η x j) := by sorry
end PDSmooth.Framework
