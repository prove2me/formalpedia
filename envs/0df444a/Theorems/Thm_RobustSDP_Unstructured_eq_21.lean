-- Prove2me | Theorems.Thm_RobustSDP_Unstructured_eq_21
-- name    : RobustSDP.Unstructured.eq_21
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:10:45.526777+00:00
-- url     : https://prove2.me/theorems/d42bdf7c-55b6-4ac0-b901-3bb665b77334
-- title:
--   §5.1, Eq. (21) — eliminating $\tau$: $F(x) \succeq 2\rho\sqrt{\|x\|^2+1}\, I$
-- statement:
--   Let $F(x) = F_0 + \sum_{i=1}^m x_i F_i$ with symmetric $F_i \in \mathbb{R}^{n\times n}$ and let $\rho > 0$. For every $x \in \mathbb{R}^m$, there exists $\tau > 0$ with
--   $$F(x) \succeq \Bigl(\tau + \rho^2\,\frac{1 + \|x\|^2}{\tau}\Bigr) I$$
--   if and only if
--   $$F(x) \succeq 2\rho\sqrt{\|x\|^2 + 1}\; I ,$$
--   where $\|x\|^2 = \sum_i x_i^2$ is the squared Euclidean norm.
--
--   This is the step from the Schur form of (20) to the constraint of the convex problem (21), which has no auxiliary variable.
--
--   **Formalization Note** The paper says "the scalar in the left-hand side"; the scalar $\tau + \rho^2(1+\|x\|^2)/\tau$ is on the right-hand side of the displayed inequality. It also writes "the RSDP (1)" for the robust SDP (4). Neither affects the statement.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 41, §5.1, sentence before Eq. (21) and Eq. (21)

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

/-- §5.1, p. 41, (21): minimizing the scalar `τ + ρ²(1 + ‖x‖²)/τ` over `τ > 0` turns the
Schur form of (20) into the single LMI `F(x) ⪰ 2ρ√(‖x‖² + 1) · I` of (21). -/
theorem eq_21 {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ) :
    (∃ τ : ℝ, 0 < τ ∧ (affineMap Fs x -
        (τ + ρ ^ 2 * (1 + ∑ i, x i ^ 2) / τ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef) ↔
      (affineMap Fs x -
        (2 * ρ * Real.sqrt (∑ i, x i ^ 2 + 1)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by sorry

end RobustSDP.Unstructured
