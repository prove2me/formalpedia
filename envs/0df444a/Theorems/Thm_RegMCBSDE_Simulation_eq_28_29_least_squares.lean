-- Prove2me | Theorems.Thm_RegMCBSDE_Simulation_eq_28_29_least_squares
-- name    : RegMCBSDE.Simulation.eq_28_29_least_squares
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:50.475011+00:00
-- url     : https://prove2.me/theorems/b9ec0de7-d236-4579-bc18-77131666ec8c
-- title:
--   Proof of Theorem 3, Eqs. (28)–(29) — empirical least squares: θ_x = [V^M]⁻¹(1/M)Σ v^m x^m and λ_min|θ_x|² ≤ |θ_x·v|²_M ≤ |x|²_M
-- statement:
--   Let $M\ge1$, let $x=(x^m)_{1\le m\le M}$ be real numbers and $(v^m)_{1\le m\le M}$ vectors of $\mathbb R^n$, and suppose that $V^M=\frac1M\sum_{m=1}^Mv^m[v^m]^*$ is invertible, i.e. $\lambda_{\min}(V^M)>0$. For $y\in\mathbb R^M$ write $|y|_M^2=\frac1M\sum_{m=1}^M|y_m|^2$. Then
--
--   1. the vector
--   $$\theta_x=\frac{[V^M]^{-1}}{M}\sum_{m=1}^Mv^mx^m \qquad (28)$$
--   is the unique minimizer of $\theta\mapsto|x-\theta\cdot v|_M^2$;
--   2. the map $x\mapsto\theta_x$ is linear;
--   3. for every $c\le\lambda_{\min}(V^M)$,
--   $$c\,|\theta_x|^2\le|\theta_x\cdot v|^2_M\le|x|^2_M. \qquad (29)$$
--
--   This is the empirical counterpart of the contraction property of $\mathbf L_2$ projections, and it is the tool behind every bound on the empirical regression coefficients in the proof of Theorem 3.
--
--   **Formalization Note** The vectors are indexed by an arbitrary finite type. Invertibility is stated as positive definiteness of $V^M$ (equivalent, since $V^M$ is positive semidefinite). Inequality (29) with $\lambda_{\min}(V^M)$ is stated for every $c$ with $c|y|^2\le y^*V^My$ for all $y$, which is the set $c\le\lambda_{\min}(V^M)$.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, p. 18, Proof of Theorem 3, Eqs. (28)–(29)

import Mathlib
import Definitions.Def_RegMCBSDE_Simulation_Setting

namespace RegMCBSDE.Simulation

/-- Proof of Theorem 3, Eqs. (28)–(29), p. 18: the empirical least-squares problem in `ℝ^M`.
Let `x^1, …, x^M ∈ ℝ` and `v^1, …, v^M ∈ ℝ^ι`, `M ≥ 1`, and suppose
`V^M = (1/M) ∑_m v^m [v^m]^*` is invertible (positive definite, `λ_min(V^M) > 0`). Then
`θ_x = (V^M)^{-1} (1/M) ∑_m v^m x^m` (28) is the unique minimizer of `θ ↦ |x - θ·v|²_M`, where
`|y|²_M = (1/M) ∑_m y_m²`; the map `x ↦ θ_x` is linear; and for every `c ≤ λ_min(V^M)` (encoded as
`c |y|² ≤ y^* V^M y` for all `y`), `c |θ_x|² ≤ |θ_x·v|²_M ≤ |x|²_M` (29). -/
theorem eq_28_29_least_squares {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ℕ) (hM : 0 < M)
    (v : Fin M → ι → ℝ)
    (hV : ((1 / (M : ℝ)) • ∑ s, Matrix.vecMulVec (v s) (v s)).PosDef) :
    let V : Matrix ι ι ℝ := (1 / (M : ℝ)) • ∑ s, Matrix.vecMulVec (v s) (v s)
    let empSq : (Fin M → ℝ) → ℝ := fun y => (1 / (M : ℝ)) * ∑ s, y s ^ 2
    let θ : (Fin M → ℝ) → (ι → ℝ) := fun x => V⁻¹.mulVec ((1 / (M : ℝ)) • ∑ s, x s • v s)
    (∀ x : Fin M → ℝ, ∀ θ' : ι → ℝ, θ' ≠ θ x →
        empSq (fun s => x s - θ x ⬝ᵥ v s) < empSq (fun s => x s - θ' ⬝ᵥ v s)) ∧
    (∀ (a b : ℝ) (x y : Fin M → ℝ), θ (a • x + b • y) = a • θ x + b • θ y) ∧
    (∀ (c : ℝ), (∀ y : ι → ℝ, c * sqn y ≤ y ⬝ᵥ V.mulVec y) → ∀ x : Fin M → ℝ,
        c * sqn (θ x) ≤ empSq (fun s => θ x ⬝ᵥ v s) ∧ empSq (fun s => θ x ⬝ᵥ v s) ≤ empSq x) := by sorry

end RegMCBSDE.Simulation
