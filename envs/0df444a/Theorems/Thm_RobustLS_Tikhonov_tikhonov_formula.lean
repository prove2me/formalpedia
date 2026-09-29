-- Prove2me | Theorems.Thm_RobustLS_Tikhonov_tikhonov_formula
-- name    : RobustLS.Tikhonov.tikhonov_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:31:36.434362+00:00
-- url     : https://prove2.me/theorems/01b18f8b-8dcf-4a56-88c4-23ec2997a45a
-- title:
--   Theorem 3.2, proof — x = (AᵀA + µI)⁻¹Aᵀb with µ = (λ − τ)/τ = ‖Ax − b‖/√(‖x‖² + 1)
-- statement:
--   Let $A \in \mathbb R^{n\times m}$ and $b \in \mathbb R^n$ (Euclidean norms). Let $(x, \lambda, \tau)$ be an optimal point of the second-order cone program (15),
--   $$\text{minimize } \lambda \quad\text{subject to}\quad \|Ax - b\| \le \lambda - \tau,\qquad \left\|\begin{bmatrix} x \\ 1\end{bmatrix}\right\| \le \tau,$$
--   with $\lambda > \tau$, and let $z \in \mathbb R^n$, $u \in \mathbb R^m$ satisfy the dual constraint $A^\top z + u = 0$ together with the values of the dual optimal point,
--   $$z = -\frac{Ax - b}{\|Ax - b\|},\qquad u = -\frac{x}{\sqrt{\|x\|^2 + 1}}.$$
--   Then, with $\mu = (\lambda - \tau)/\tau$,
--   $$\mu = \frac{\|Ax - b\|}{\sqrt{\|x\|^2 + 1}} \qquad\text{and}\qquad x = \big(A^\top A + \mu I\big)^{-1} A^\top b.$$
--
--   This is the step of the proof that turns the dual certificate into the closed form of the robust solution: a Tikhonov-regularized least-squares solution whose regularization parameter is the ratio of the residual to $\sqrt{\|x\|^2+1}$.
--
--   **Formalization Note** The inverse is Mathlib's matrix inverse; under the hypotheses $\mu > 0$, so $A^\top A + \mu I$ is positive definite and the inverse is the genuine one.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1041 (PDF p. 7), Theorem 3.2, proof, last display

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with Uncertain Data*,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Theorem 3.2, proof, p. 1041 (PDF p. 7):
"Replace these values in Aᵀz + u = 0 to obtain the expression of the optimal x:
x = (AᵀA + µI)⁻¹Aᵀb, with µ = (λ − τ)/τ = ‖Ax − b‖/√(‖x‖² + 1)."

Setting: `(x, λ, τ)` is optimal for the SOCP (15) with `λ > τ`, and `z ∈ ℝ^n`, `u ∈ ℝ^m` satisfy
`Aᵀz + u = 0` together with the values found in the previous step,
`z = −(Ax − b)/‖Ax − b‖` and `u = −x/√(‖x‖² + 1)`. Then `µ = (λ − τ)/τ` equals
`‖Ax − b‖/√(‖x‖² + 1)` and `x = (AᵀA + µI)⁻¹Aᵀb`.

`⁻¹` is Mathlib's matrix inverse; under these hypotheses `µ > 0`, so `AᵀA + µI` is positive
definite and the inverse is the genuine one. -/
theorem tikhonov_formula {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (z : Fin n → ℝ) (u : Fin m → ℝ)
    (hopt : IsSOCPOptimal A b x lam tau) (hlt : tau < lam)
    (hlin : Aᵀ *ᵥ z + u = 0)
    (hz : z = (-(1 / eucNorm (A *ᵥ x - b))) • (A *ᵥ x - b))
    (hu : u = (-(1 / Real.sqrt (eucNorm x ^ 2 + 1))) • x) :
    (lam - tau) / tau = eucNorm (A *ᵥ x - b) / Real.sqrt (eucNorm x ^ 2 + 1) ∧
      x = (Aᵀ * A + ((lam - tau) / tau) • (1 : Matrix (Fin m) (Fin m) ℝ))⁻¹ *ᵥ (Aᵀ *ᵥ b) := by sorry

end RobustLS.Tikhonov
