-- Prove2me | Theorems.Thm_RobinsonSR_NLP_kkt_strongly_regular_iff
-- name    : RobinsonSR.NLP.kkt_strongly_regular_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:39:29.3582+00:00
-- url     : https://prove2.me/theorems/97cf939e-6530-4b90-ba44-b6a6bd6f80d9
-- title:
--   §4, p. 55 — (4.3) is strongly regular iff (4.5) is nonsingular and its Schur complement (4.6) is a P-matrix
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$ be open, $x_0\in\Omega$, and let $\theta:\mathbb R^n\to\mathbb R$, $g:\mathbb R^n\to\mathbb R^p$, $h:\mathbb R^n\to\mathbb R^q$ be differentiable on $\Omega$ and twice differentiable at $x_0$ (each gradient $\nabla\theta$, $\nabla g_i$, $\nabla h_j$ is differentiable at $x_0$). Let $u_0\in\mathbb R^p$, $v_0\in\mathbb R^q$ be such that $(x_0,u_0,v_0)$ solves the KKT generalized equation
--   $$0\in\begin{bmatrix}\mathcal L'(x,u,v)\\-g(x)\\-h(x)\end{bmatrix}+\partial\psi_{\mathbb R^n\times\mathbb R^p_+\times\mathbb R^q}\begin{bmatrix}x\\u\\v\end{bmatrix}.\qquad(4.3)$$
--   Write $\mathcal L''=\mathcal L''(x_0,u_0,v_0)$, $H=h'(x_0)$, $G^+$ for the matrix with rows $\nabla g_i(x_0)$, $u_{0,i}>0$, and $G^0$ for the matrix with rows $\nabla g_i(x_0)$, $g_i(x_0)=0=u_{0,i}$. Then (4.3) is strongly regular at $(x_0,u_0,v_0)$ if and only if the matrix
--   $$\begin{bmatrix}\mathcal L''&H^{T}&G^{+T}\\-H&0&0\\-G^{+}&0&0\end{bmatrix}\qquad(4.5)$$
--   is nonsingular and its Schur complement
--   $$\begin{bmatrix}G^0&0&0\end{bmatrix}\begin{bmatrix}\mathcal L''&H^{T}&G^{+T}\\-H&0&0\\-G^{+}&0&0\end{bmatrix}^{-1}\begin{bmatrix}G^{0T}\\0\\0\end{bmatrix}\qquad(4.6)$$
--   is a P-matrix.
--
--   This is the paper's application of its §3 Schur-complement criterion and its reduction to the KKT system; Theorem 4.1 is proved by verifying both conditions.
--
--   **Formalization Note** $\mathcal L''$ enters through its matrix in the standard basis. When no constraint is weakly active ($g^0(x_0)$ vacuous), the Schur complement is a $0\times0$ matrix, which is a P-matrix vacuously, so the statement reduces to nonsingularity of (4.5), as the page remarks. Nonsingularity is kept as a conjunct because Mathlib's inverse of a singular matrix is $0$.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), pp. 54–55, (4.3)–(4.6)

import Mathlib
import Definitions.Def_RobinsonSR_NLP_Setting
open scoped RealInnerProductSpace Matrix

namespace RobinsonSR.NLP

/-- §4, p. 55: let `θ, g, h` be differentiable on an open set `Ω ⊆ ℝⁿ` and twice differentiable at
`x₀ ∈ Ω`, and let `(x₀, u₀, v₀)` solve the KKT generalized equation (4.3). Then (4.3) is strongly
regular at `(x₀, u₀, v₀)` if and only if the matrix (4.5) built from `ℒ″`, `H = h′(x₀)` and
`G⁺` (rows `∇gᵢ(x₀)` with `u₀ᵢ > 0`) is nonsingular and the Schur complement (4.6), with `G⁰`
(rows `∇gᵢ(x₀)` with `gᵢ(x₀) = 0 = u₀ᵢ`), is a P-matrix. -/
theorem kkt_strongly_regular_iff {n p q : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩ : IsOpen Ω) (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ Ω)
    (θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin q))
    (hθ : DifferentiableOn ℝ θ Ω)
    (hg : ∀ i, DifferentiableOn ℝ (fun x => g x i) Ω)
    (hh : ∀ j, DifferentiableOn ℝ (fun x => h x j) Ω)
    (hθ2 : DifferentiableAt ℝ (gradient θ) x0)
    (hg2 : ∀ i, DifferentiableAt ℝ (gradient (fun x => g x i)) x0)
    (hh2 : ∀ j, DifferentiableAt ℝ (gradient (fun x => h x j)) x0)
    (u0 : EuclideanSpace ℝ (Fin p)) (v0 : EuclideanSpace ℝ (Fin q))
    (hsol : -(kktMap θ g h (mk x0 u0 v0)) ∈ RobinsonSR.Reduction.normalCone (kktCone n p q) (mk x0 u0 v0)) :
    StronglyRegularAt (kktMap θ g h) (kktCone n p q) (mk x0 u0 v0) ↔
      ((kktMatrix (hessMatrix θ g h x0 u0 v0) (eqJacobian h x0)
          (ineqJacobian g x0 (fun i => 0 < u0 i))).det ≠ 0 ∧
        IsPMatrix (schurS (hessMatrix θ g h x0 u0 v0) (eqJacobian h x0)
          (ineqJacobian g x0 (fun i => 0 < u0 i))
          (ineqJacobian g x0 (fun i => g x0 i = 0 ∧ u0 i = 0)))) := by sorry

end RobinsonSR.NLP
