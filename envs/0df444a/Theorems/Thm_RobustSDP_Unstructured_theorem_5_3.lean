-- Prove2me | Theorems.Thm_RobustSDP_Unstructured_theorem_5_3
-- name    : RobustSDP.Unstructured.theorem_5_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:11:52.38499+00:00
-- url     : https://prove2.me/theorems/2117f267-b783-4f56-983d-3d8faadb3379
-- title:
--   Theorem 5.3 — robust largest-eigenvalue minimization: worst case $\lambda_{\max}(F(x)) + 2\rho\sqrt{\|x\|^2+1}$
-- statement:
--   Let $F(x) = F_0 + \sum_{i=1}^m x_i F_i$ with symmetric $F_i \in \mathbb{R}^{n\times n}$, let $\rho > 0$, and let $\mathbf{F}(x,\Delta) = F(x) + \Delta_0 + \Delta_0^T + \sum_i x_i(\Delta_i + \Delta_i^T)$ be the unstructured perturbation of §5.1, $\Delta = [\Delta_0 \cdots \Delta_m]$ normed by its largest singular value. Then for every $x \in \mathbb{R}^m$ and every $t \in \mathbb{R}$,
--   $$tI \succeq \mathbf{F}(x,\Delta)\ \text{ for every } \Delta \text{ with } \|\Delta\|\le\rho \quad\Longleftrightarrow\quad \bigl(t - 2\rho\sqrt{\|x\|^2+1}\bigr) I \succeq F(x),$$
--   with $\|x\|^2 = \sum_i x_i^2$. Equivalently (for $n \ge 1$),
--   $$\sup_{\|\Delta\| \le \rho} \lambda_{\max}(\mathbf{F}(x,\Delta)) = \lambda_{\max}(F(x)) + 2\rho\sqrt{\|x\|^2 + 1},$$
--   so the robust version of the eigenvalue minimization problem (24) has the same objective as the convex problem (25), and hence the same optimal value and solutions.
--
--   **Formalization Note** The statement is the epigraph form of the worst-case identity: $\lambda_{\max}(M) \le t$ is written $tI - M \succeq 0$, which avoids defining $\lambda_{\max}$ and any supremum. The theorem says "the min-max problem (24)"; (24) is the nominal problem, and the min-max problem meant is its robust version. The second and third sentences (uniqueness, Lipschitz stability, the limit $\rho \to 0$) are not part of this statement.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 43, §5.4, Eq. (24), Eq. (25) and Theorem 5.3 (first sentence)

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

/-- Theorem 5.3 (first sentence), §5.4, p. 43, in epigraph form: for every `x` and
every scalar `t`, `t` bounds the largest eigenvalue of `F(x, Δ)` for every unstructured perturbation
`‖[Δ₀ … Δ_m]‖ ≤ ρ` (i.e. `tI ⪰ F(x, Δ)`) iff `t − 2ρ√(‖x‖² + 1)` bounds the largest eigenvalue of
`F(x)` (i.e. `(t − 2ρ√(‖x‖² + 1)) I ⪰ F(x)`). Equivalently the worst-case largest eigenvalue is
`λmax(F(x)) + 2ρ√(‖x‖² + 1)`, the objective of (25). -/
theorem theorem_5_3 {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ) (t : ℝ) :
    (∀ Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ, ‖Δ‖ ≤ ρ →
        (t • (1 : Matrix (Fin n) (Fin n) ℝ) - perturbedLMI Fs Δ x).PosSemidef) ↔
      ((t - 2 * ρ * Real.sqrt (∑ i, x i ^ 2 + 1)) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        affineMap Fs x).PosSemidef := by sorry

end RobustSDP.Unstructured
