-- Prove2me | Theorems.Thm_RobustSDP_Unstructured_theorem_5_4
-- name    : RobustSDP.Unstructured.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:12:24.90705+00:00
-- url     : https://prove2.me/theorems/6a4a6cd3-ffa2-482f-aa9c-eb55d35e52ef
-- title:
--   Theorem 5.4 — robust maximum-norm minimization: worst case $\|H(x)\| + \rho\sqrt{\|x\|^2+1}$
-- statement:
--   Let $p, q \ge 1$, let $H(x) = H_0 + \sum_{i=1}^m x_i H_i$ with $H_i \in \mathbb{R}^{p\times q}$, and let $\rho > 0$. Perturb each coefficient independently,
--   $$\mathbf{H}(x,\Delta) = H_0 + \Delta_0 + \sum_{i=1}^m x_i(H_i + \Delta_i), \qquad \Delta = [\Delta_0 \cdots \Delta_m] \in \mathbb{R}^{p\times q(m+1)},$$
--   where $\|\cdot\|$ denotes the largest singular value (of $\Delta$ as one matrix). Then for every $x \in \mathbb{R}^m$ the maximum
--   $$\max_{\|\Delta\| \le \rho} \|\mathbf{H}(x,\Delta)\| = \|H(x)\| + \rho\sqrt{\|x\|^2 + 1}$$
--   is attained, with $\|x\|^2 = \sum_i x_i^2$.
--
--   Hence the min-max problem (28), $\min_x \max_{\|\Delta\|\le\rho} \|\mathbf{H}(x,\Delta)\|$, has the same objective as the convex problem (29), and so the same optimal value and solutions (the first sentence of Theorem 5.4). The robust problem is the nominal problem (27) plus a Tikhonov-type regularization term.
--
--   **Formalization Note** The worst case is stated with `IsGreatest`, so attainment is part of the claim and no real supremum is taken. $p, q \ge 1$ exclude empty matrices, for which $\|\mathbf{H}(x,\Delta)\| = 0$. The paper derives the result through "Theorem 3.2 … the SDP (15)"; the exact result is the full-perturbation Theorem 3.1. The second and third sentences (uniqueness, Lipschitz stability, the limit $\rho\to0$) are not part of this statement.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), pp. 44–45, §5.6, Eq. (27), the display defining H(x, Δ), Eq. (28), Eq. (29) and Theorem 5.4 (first sentence)

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

/-- Theorem 5.4 (first sentence), §5.6, pp. 44–45, as a closed form of the inner
maximum of (28): for every `x`, the largest value of the spectral norm `‖H(x, Δ)‖` over block rows
`Δ = [Δ₀ … Δ_m]` with `‖Δ‖ ≤ ρ` is attained and equals `‖H(x)‖ + ρ√(‖x‖² + 1)`, the objective of (29). -/
theorem theorem_5_4 {m p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (Hs : Fin (m + 1) → Matrix (Fin p) (Fin q) ℝ) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ) :
    IsGreatest {s : ℝ | ∃ Δ : Matrix (Fin p) (Fin (m + 1) × Fin q) ℝ, ‖Δ‖ ≤ ρ ∧
        s = ‖perturbedH Hs Δ x‖}
      (‖affineMap Hs x‖ + ρ * Real.sqrt (∑ i, x i ^ 2 + 1)) := by sorry

end RobustSDP.Unstructured
