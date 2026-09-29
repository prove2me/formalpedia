-- Prove2me | Theorems.Thm_RobustSDP_Unstructured_tau_pos_schur
-- name    : RobustSDP.Unstructured.tau_pos_schur
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:10:07.008498+00:00
-- url     : https://prove2.me/theorems/91c9d5ee-e8ea-4aa9-bb8d-a1484ebf54c6
-- title:
--   §5.1, p. 41 — every feasible $\tau$ in (20) is positive, and the Schur form of (20)
-- statement:
--   Let $n \ge 1$, let $F(x) = F_0 + \sum_{i=1}^m x_i F_i$ with symmetric $F_i \in \mathbb{R}^{n\times n}$, and let $\rho > 0$. For every $x \in \mathbb{R}^m$ and every $\tau \in \mathbb{R}$, the block matrix of (20)
--   $$\begin{bmatrix} F(x) - \tau I & [1\ \ x^T]\otimes \rho I \\ [1\ \ x^T]^T \otimes \rho I & \tau I \end{bmatrix}$$
--   is positive semidefinite if and only if
--   $$\tau > 0 \quad\text{and}\quad F(x) \succeq \Bigl(\tau + \rho^2\,\frac{1 + \|x\|^2}{\tau}\Bigr) I ,$$
--   where $\|x\|^2 = \sum_i x_i^2$.
--
--   This removes the large off-diagonal blocks of (20): the constraint becomes a matrix inequality of the size of the unperturbed problem, with a scalar coefficient depending on $x$ and $\tau$.
--
--   **Formalization Note** The hypothesis $n \ge 1$ is needed for the strict positivity of $\tau$: at $n = 0$ every block is empty and every $\tau$ is feasible. $F(x) \succeq cI$ is written as $F(x) - cI \succeq 0$.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 41, §5.1, paragraph after Eq. (20) and the display 'F(x) ⪰ (τ + ρ²(1 + ‖x‖²)/τ) I, τ > 0'

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

/-- §5.1, p. 41, paragraph after (20): every feasible `τ` in (20) is strictly
positive, and by Schur complements (20) is equivalent to `F(x) ⪰ (τ + ρ²(1 + ‖x‖²)/τ) I`, `τ > 0`,
where `‖x‖² = ∑ᵢ xᵢ²` is the squared Euclidean norm. -/
theorem tau_pos_schur {m n : ℕ} (hn : 0 < n) (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (ρ : ℝ) (hρ : 0 < ρ) (τ : ℝ) (x : Fin m → ℝ) :
    (lmi20 Fs ρ τ x).PosSemidef ↔
      0 < τ ∧ (affineMap Fs x -
        (τ + ρ ^ 2 * (1 + ∑ i, x i ^ 2) / τ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by sorry

end RobustSDP.Unstructured
