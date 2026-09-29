-- Prove2me | Theorems.Thm_RobustLS_Tikhonov_dual_optimal_point
-- name    : RobustLS.Tikhonov.dual_optimal_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:30:55.495979+00:00
-- url     : https://prove2.me/theorems/a80ce2ce-13b9-43ad-be84-a202a526f1ad
-- title:
--   Theorem 3.2, proof — the dual optimal point is z = −(Ax − b)/‖Ax − b‖, [u; v] = −[x; 1]/√(‖x‖² + 1)
-- statement:
--   Let $A \in \mathbb R^{n\times m}$ and $b \in \mathbb R^n$ (Euclidean norms). Let $(x, \lambda, \tau)$ be an optimal point of the second-order cone program (15),
--   $$\text{minimize } \lambda \quad\text{subject to}\quad \|Ax - b\| \le \lambda - \tau,\qquad \left\|\begin{bmatrix} x \\ 1\end{bmatrix}\right\| \le \tau,$$
--   with $\lambda > \tau$. Let $(z, u, v)$ be feasible for the dual of (15), i.e. $A^\top z + u = 0$, $\|z\| \le 1$ and $\left\|\begin{bmatrix} u \\ v\end{bmatrix}\right\| \le 1$, with dual objective equal to the primal optimal value, $b^\top z - v = \lambda$. Then
--   $$z = -\frac{Ax - b}{\|Ax - b\|} \qquad\text{and}\qquad \begin{bmatrix} u \\ v\end{bmatrix} = -\frac{1}{\sqrt{\|x\|^2 + 1}}\begin{bmatrix} x \\ 1\end{bmatrix}.$$
--
--   The dual optimal point is thus determined explicitly by the primal optimal $x$; substituting it into the dual constraint $A^\top z + u = 0$ yields the formula of Theorem 3.2.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1041 (PDF p. 7), Theorem 3.2, proof (display following Eq. (18))

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with Uncertain Data*,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Theorem 3.2, proof, p. 1041 (PDF p. 7):
"Using ‖z‖ ≤ 1, ‖[uᵀ v]ᵀ‖ ≤ 1, u = −Aᵀz, we get
z = −(Ax − b)/‖Ax − b‖ and [uᵀ v] = −[xᵀ 1]/√(‖x‖² + 1)."

Setting of the sentence: `(x, λ, τ)` is optimal for the SOCP (15) with `λ > τ`, and `(z, u, v)`
is a dual feasible point whose objective equals the primal optimal value, `bᵀz − v = λ`
(Eq. (18)). Then `z = −(Ax − b)/‖Ax − b‖` and `[u; v] = −[x; 1]/√(‖x‖² + 1)`. -/
theorem dual_optimal_point {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (z : Fin n → ℝ) (u : Fin m → ℝ) (v : ℝ)
    (hopt : IsSOCPOptimal A b x lam tau) (hlt : tau < lam) (hfeas : IsDualFeasible A z u v)
    (hval : b ⬝ᵥ z - v = lam) :
    z = (-(1 / eucNorm (A *ᵥ x - b))) • (A *ᵥ x - b) ∧
      stackScalar u v = (-(1 / Real.sqrt (eucNorm x ^ 2 + 1))) • stackOne x := by sorry

end RobustLS.Tikhonov
