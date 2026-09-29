-- Prove2me | Theorems.Thm_RobustSDP_FullPert_theorem_3_1
-- name    : RobustSDP.FullPert.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:59:55.197783+00:00
-- url     : https://prove2.me/theorems/44d0819a-41bf-4822-a06e-77fb635aab6e
-- title:
--   Theorem 3.1 — Under full LFR perturbations the robust feasible set is the projection of one LMI
-- statement:
--   Consider the perturbation model of El Ghaoui, Oustry and Lebret: symmetric matrices $F_0, \dots, F_m \in \mathbb{R}^{n\times n}$ defining $F(x) = F_0 + \sum_i x_i F_i$, matrices $R_0, \dots, R_m \in \mathbb{R}^{q\times n}$ defining $R(x) = R_0 + \sum_i x_i R_i$, and fixed $L \in \mathbb{R}^{n\times p}$, $D \in \mathbb{R}^{q\times p}$. Take full perturbations $\mathcal{D} = \mathbb{R}^{p\times q}$, a level $\rho > 0$, and assume the standing hypothesis $\|D\| < \rho^{-1}$ of §3.1 (spectral norm), $q \ge 1$ and $L \neq 0$. Let $\mathcal{X}_\rho$ be the robust feasible set (2): the $x \in \mathbb{R}^m$ such that, for every $\Delta$ with $\|\Delta\| \le \rho$, $\det(I - D\Delta) \neq 0$ and $\mathbf{F}(x,\Delta) = F(x) + L\Delta(I - D\Delta)^{-1}R(x) + R(x)^T(I - \Delta^TD^T)^{-1}\Delta^TL^T \succeq 0$. Then for every $x \in \mathbb{R}^m$,
--   $$x \in \mathcal{X}_\rho \quad\Longleftrightarrow\quad \exists\, \tau \in \mathbb{R}:\ \begin{bmatrix} F(x) - \tau LL^T & R(x)^T - \tau LD^T \\ R(x) - \tau DL^T & \tau(\rho^{-2}I - DD^T)\end{bmatrix} \succeq 0. \qquad (10)$$
--
--   The paper states Theorem 3.1 as: the robust SDP (4), minimize $c^Tx$ over $\mathcal{X}_\rho$, and a corresponding solution $x$ can be computed by solving the SDP in the variables $(x, \tau)$ that minimizes $c^Tx$ subject to (10). The two problems have the same objective, so the displayed identity between $\mathcal{X}_\rho$ and the projection onto $x$ of the feasible set of (10) is the mathematical content of that sentence: the optimal values coincide and the optimal $x$ of the robust problem are exactly the $x$-parts of the optimal $(x,\tau)$ of the SDP. The robust problem, a semi-infinite program, is therefore an ordinary SDP.
--
--   **Formalization Note** "Can be computed by solving" is read as the set identity above, for every $x$. The hypothesis $L \neq 0$ is **added**: the printed statement fails for $L = 0$ (with $n = p = q = 1$, $m = 0$, $F = 0$, $D = 0$, $R = 1$, the robust feasible set is everything while (10) is $\begin{bmatrix}0 & 1\\1 & \tau(\rho^{-2})\end{bmatrix} \succeq 0$, infeasible). $q \ge 1$ makes "matrices of appropriate size" explicit. The standing assumptions $\rho > 0$ (§3) and $\|D\| < \rho^{-1}$ (§3.1) are hypotheses. The objective vector $c$ plays no role in the set identity; the solution correspondence is stated separately in `theorem_3_1_solutions`.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 36, Theorem 3.1, Eq. (10)

import Mathlib
import Definitions.Def_RobustSDP_FullPert_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.FullPert

/-- Theorem 3.1, p. 36, as a set identity. Full perturbations `𝒟 = ℝ^{p×q}` (`⊤`), `ρ > 0`,
the standing hypothesis `‖D‖ < ρ⁻¹` of §3.1, `F₀, …, F_m` symmetric, `q ≥ 1`, and `L ≠ 0`
(added: the printed statement fails for `L = 0`). Then `x` lies in the robust feasible set
`𝒳_ρ` (2) iff there is `τ` making the block matrix of the SDP (10) positive semidefinite.
Since (4) and (10) share the objective `cᵀx`, this is the content of "the RSDP (4) and a
corresponding solution `x` can be computed by solving the SDP (10)". -/
theorem theorem_3_1 {m n p q : ℕ} (hq : 0 < q)
    (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (hFs : ∀ i, (Fs i).IsSymm)
    (Rs : Fin (m + 1) → Matrix (Fin q) (Fin n) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (D : Matrix (Fin q) (Fin p) ℝ) (hL : L ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) (hD : ‖D‖ < ρ⁻¹)
    (x : Fin m → ℝ) :
    x ∈ robustFeasibleSet Fs Rs L D ⊤ ρ ↔
      ∃ τ : ℝ, (sdpLMI (affineMap Fs x) (affineMap Rs x) L D ρ τ).PosSemidef := by sorry

end RobustSDP.FullPert
