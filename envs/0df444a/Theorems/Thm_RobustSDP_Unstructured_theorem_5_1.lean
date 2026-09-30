-- Prove2me | Theorems.Thm_RobustSDP_Unstructured_theorem_5_1
-- name    : RobustSDP.Unstructured.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:11:12.160862+00:00
-- url     : https://prove2.me/theorems/98abacd8-86df-4588-b2b8-4fa6041fe506
-- title:
--   Theorem 5.1 — the robust LMI under unstructured perturbations is $F(x) \succeq 2\rho\sqrt{\|x\|^2+1}\, I$
-- statement:
--   Let $F(x) = F_0 + \sum_{i=1}^m x_i F_i$ with symmetric $F_0, \dots, F_m \in \mathbb{R}^{n\times n}$, and let $\rho > 0$. Perturb every coefficient matrix independently:
--   $$\mathbf{F}(x,\Delta) = F(x) + \Delta_0 + \Delta_0^T + \sum_{i=1}^m x_i(\Delta_i + \Delta_i^T), \qquad \Delta = [\Delta_0 \cdots \Delta_m] \in \mathbb{R}^{n\times n(m+1)},$$
--   where the size of $\Delta$ is measured by the largest singular value $\|\Delta\|$ of the whole block row. Then for every $x \in \mathbb{R}^m$,
--   $$\mathbf{F}(x,\Delta) \succeq 0 \ \text{ for every } \Delta \text{ with } \|\Delta\| \le \rho \quad\Longleftrightarrow\quad F(x) \succeq 2\rho\sqrt{\|x\|^2 + 1}\; I,$$
--   where $\|x\|^2 = \sum_i x_i^2$ is the squared Euclidean norm.
--
--   Hence the robust SDP "minimize $c^Tx$ subject to $\mathbf{F}(x,\Delta) \succeq 0$ for all $\|\Delta\| \le \rho$" and the convex problem (21) "minimize $c^Tx$ subject to $F(x) \succeq 2\rho\sqrt{\|x\|^2+1}\,I$" have the same objective and the same feasible set, so the same optimal value and the same solutions. This is the first sentence of Theorem 5.1; it exhibits robustification against unstructured perturbations as a regularization of the nominal constraint.
--
--   **Formalization Note** "The optimal value of the RSDP can be computed by solving (21)" is formalized as the identity of the two feasible sets, stated for every $x$, from which equality of values and of solution sets follows. The theorem's second sentence (uniqueness and regularity of the solution under hypotheses H1 and H2) is not part of this statement. $\|\Delta\|$ is Mathlib's $\ell^2$ operator norm of the $n\times n(m+1)$ matrix, not a combination of block norms.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 41, Theorem 5.1 (first sentence), with the model of §5.1 and Eq. (21)

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

/-- Theorem 5.1 (first sentence), p. 41, read as an identity of feasible sets: under
unstructured perturbations `F(x, Δ) = F(x) + Δ₀ + Δ₀ᵀ + ∑ᵢ xᵢ(Δᵢ + Δᵢᵀ)` with `‖[Δ₀ … Δ_m]‖ ≤ ρ`
(spectral norm), `x` is robustly feasible iff `F(x) ⪰ 2ρ√(‖x‖² + 1) · I` (the constraint of (21)),
where `‖x‖² = ∑ᵢ xᵢ²`. Hence the RSDP and (21) have the same objective, feasible set, optimal value
and solutions. -/
theorem theorem_5_1 {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (ρ : ℝ) (hρ : 0 < ρ) (x : Fin m → ℝ) :
    x ∈ robustFeasibleSet Fs ρ ↔
      (affineMap Fs x -
        (2 * ρ * Real.sqrt (∑ i, x i ^ 2 + 1)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by sorry

end RobustSDP.Unstructured
