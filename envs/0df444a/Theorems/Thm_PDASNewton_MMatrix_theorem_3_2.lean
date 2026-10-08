-- Prove2me | Theorems.Thm_PDASNewton_MMatrix_theorem_3_2
-- name    : PDASNewton.MMatrix.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:13.603366+00:00
-- url     : https://prove2.me/theorems/a06a0a4b-9438-4b66-a001-433064fcf99e
-- title:
--   Theorem 3.2, p. 7 — for an M-matrix, xᵏ → x* from arbitrary initial data, y* ≤ yᵏ⁺¹ ≤ yᵏ (k ≥ 1), yᵏ ≤ ψ (k ≥ 2)
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be an M-matrix (nonsingular, $a_{ij}\le 0$ for $i\ne j$, $A^{-1}\ge0$), let $f,\psi\in\mathbb{R}^n$ and $c>0$, and let $x^* = (y^*,\lambda^*)$ be the solution of the complementarity problem (3.1),
--   $$Ay + \lambda = f, \qquad \lambda - \max(0, \lambda + c(y-\psi)) = 0 .$$
--   Let $x^k = (y^k,\lambda^k)$ be the iterates of the primal-dual active set algorithm: with $\mathcal{A}_k = \{i : \lambda^k_i + c(y^k-\psi)_i > 0\}$ and $\mathcal{I}_k$ its complement, $(y^{k+1},\lambda^{k+1})$ solves $Ay^{k+1}+\lambda^{k+1} = f$, $y^{k+1} = \psi$ on $\mathcal{A}_k$, $\lambda^{k+1} = 0$ on $\mathcal{I}_k$. Then, for arbitrary initial data $(y^0,\lambda^0)$,
--   $$x^k \to x^*, \qquad y^* \le y^{k+1} \le y^k \ \ (k\ge1), \qquad y^k \le \psi \ \ (k \ge 2).$$
--
--   This is the global convergence and monotonicity theorem of the paper: for M-matrices the primal-dual active set strategy (equivalently, the semismooth Newton method) converges from any starting point, with monotonically decreasing, feasible primal iterates.
--
--   **Formalization Note** The solution $(y^*,\lambda^*)$ is a hypothesis; for an M-matrix it exists and is unique (Berman–Plemmons). Convergence is in the product topology of $\mathbb{R}^n\times\mathbb{R}^n$. The paper's matrix is written $A$ and the active set $\mathcal{A}$; in Lean the active set is `activeSet`. The algorithm's stopping option is not modelled; that a run exists from every initial pair is the separate item `run_exists`.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 7, Theorem 3.2 (proof: Appendix A, p. 20)

import Mathlib
import Definitions.Def_PDASNewton_MMatrix_Setting

open Filter Topology Matrix

namespace PDASNewton.MMatrix

theorem theorem_3_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : IsMMatrix A) (ystar lamstar : Fin n → ℝ)
    (hsol : PDASNewton.Local.IsSolution A f ψ c ystar lamstar) (y lam : ℕ → Fin n → ℝ)
    (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    Tendsto (fun k => (y k, lam k)) atTop (𝓝 (ystar, lamstar)) ∧
      (∀ k, 1 ≤ k → ystar ≤ y (k + 1) ∧ y (k + 1) ≤ y k) ∧
      (∀ k, 2 ≤ k → y k ≤ ψ) := by sorry

end PDASNewton.MMatrix
