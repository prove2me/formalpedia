-- Prove2me | Theorems.Thm_RobustSDP_Unstructured_theorem_5_2
-- name    : RobustSDP.Unstructured.theorem_5_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:11:32.433146+00:00
-- url     : https://prove2.me/theorems/fa52e1fd-cb23-4922-866b-56b24f2f1cc0
-- title:
--   Theorem 5.2 — the robust LP is the second-order cone program (23)
-- statement:
--   Consider the linear constraints $a_i^T x \ge b_i$, $i = 1, \dots, K$, with $a_i \in \mathbb{R}^m$, $b_i \in \mathbb{R}$, and let $\rho > 0$. Suppose the data of each constraint are perturbed independently: the perturbed value of $[a_i^T\ b_i]^T$ is $[a_i^T\ b_i]^T + \delta_i$ with $\delta_i = (\delta a_i, \delta b_i) \in \mathbb{R}^{m+1}$ and $\|\delta_i\|_2 \le \rho$. Then for every $x \in \mathbb{R}^m$, the perturbed constraints $(a_i + \delta a_i)^T x \ge b_i + \delta b_i$ hold for every $i$ and every admissible $\delta_i$ if and only if
--   $$a_i^T x - \rho\sqrt{\|x\|_2^2 + 1} \ge b_i, \qquad i = 1, \dots, K .$$
--
--   Hence the robust LP "minimize $c^Tx$ subject to the perturbed constraints for all admissible perturbations" and the convex problem (23) have the same feasible set, optimal value and solutions (the first sentence of Theorem 5.2). Problem (23) is a second-order cone program.
--
--   **Formalization Note** The paper numbers the constraints $1, \dots, L$; the count is called $K$ here. $\|\delta_i\|_2 \le \rho$ is written $\sum_j \delta a_{ij}^2 + \delta b_i^2 \le \rho^2$, and $\|x\|_2^2 = \sum_j x_j^2$. The theorem's second sentence (uniqueness and regularity under H1, H2 for $0 < \rho < \rho_{\max}$) is not part of this statement.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), pp. 42–43, §5.3, the perturbation model, Eq. (23) and Theorem 5.2 (first sentence)

import Mathlib
import Definitions.Def_RobustSDP_Unstructured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

/-- Theorem 5.2 (first sentence), §5.3, pp. 42–43, read as an identity of feasible
sets: the constraints `aᵢᵀx ≥ bᵢ` (`i = 1, …, K`) hold for every perturbation
`[aᵢᵀ bᵢ]ᵀ + δᵢ` with `‖δᵢ‖₂ ≤ ρ` (each `δᵢ = (δaᵢ, δbᵢ) ∈ ℝ^{m+1}` chosen independently) iff
`aᵢᵀx − ρ√(‖x‖₂² + 1) ≥ bᵢ` for every `i` (the constraints of (23)). -/
theorem theorem_5_2 {m K : ℕ} (a : Fin K → Fin m → ℝ) (b : Fin K → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (x : Fin m → ℝ) :
    (∀ i : Fin K, ∀ δa : Fin m → ℝ, ∀ δb : ℝ, ∑ j, δa j ^ 2 + δb ^ 2 ≤ ρ ^ 2 →
        (a i + δa) ⬝ᵥ x ≥ b i + δb) ↔
      ∀ i : Fin K, a i ⬝ᵥ x - ρ * Real.sqrt (∑ j, x j ^ 2 + 1) ≥ b i := by sorry

end RobustSDP.Unstructured
