-- Prove2me | Theorems.Thm_RobustSDP_Structured_theorem_5_6
-- name    : RobustSDP.Structured.theorem_5_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:03:46.583233+00:00
-- url     : https://prove2.me/theorems/a0c8ed01-1343-4dc5-ad22-8c97103f986a
-- title:
--   Theorem 5.6 — an SDP sufficient condition for integer solutions of a feasibility SDP by robust rounding
-- statement:
--   Let $F(x) = F_0 + \sum_{i=1}^m x_i F_i$ with symmetric $F_0,\dots,F_m \in \mathbb{R}^{n\times n}$, and consider the feasibility problem (32): find an integer vector $x \in \mathbb{Z}^m$ with $F(x) \succeq 0$. For $i = 1,\dots,m$ write
--   $$F_i = 2L_iR_i, \qquad L_i,\ R_i^T \in \mathbb{R}^{n\times r_i}, \qquad r_i = \operatorname{rank} F_i,$$
--   put $L = [L_1\ \cdots\ L_m]$ and $R = [R_1; \dots; R_m]$, and let $\mathcal{S}$ be the set of block-diagonal matrices $\operatorname{diag}(S_1,\dots,S_m)$ with $S_i \in \mathbb{R}^{r_i\times r_i}$.
--
--   Suppose $x_{\mathrm{feas}} \in \mathbb{R}^m$ satisfies, for some $\lambda \ge 0$, $S = S^T \in \mathcal{S}$ and $G = -G^T \in \mathcal{S}$,
--   $$\begin{bmatrix} F(x_{\mathrm{feas}}) - \lambda I - LSL^T & \tfrac12 R^T + LG \\ \tfrac12 R - GL^T & S\end{bmatrix} \succ 0.$$
--   Then every integer vector $z \in \mathbb{Z}^m$ closest to $x_{\mathrm{feas}}$ in the maximum norm, i.e. with $\|z - x_{\mathrm{feas}}\|_\infty \le \|z' - x_{\mathrm{feas}}\|_\infty$ for all $z' \in \mathbb{Z}^m$, satisfies
--   $$F(z) \succeq 0,$$
--   so it solves (32).
--
--   The theorem applies the structured robustness analysis of Section 3.2 to error-in-variables problems: robustness of $F$ against perturbations of $x$ of size $1/2$ in each coordinate turns an SDP-feasible point into an integer solution by rounding. The integer feasibility problem itself is NP-hard in general.
--
--   **Formalization Note** The block structure is indexed by the sigma type $\Sigma_i \{0,\dots,r_i-1\}$; $\mathcal{S}$ is expressed through Mathlib's `blockDiagonal'` of a family of blocks. The hypothesis $r_i = \operatorname{rank} F_i$ is kept as on the page; the conclusion does not depend on it. The paper's definition of $\mathcal{S}$ writes "$i = 1,\dots,n$", a slip for $i = 1,\dots,m$. The maximum norm is Mathlib's sup norm on `Fin m → ℝ`; $\succ 0$ and $\succeq 0$ are `Matrix.PosDef` and `Matrix.PosSemidef`. The printed $G$-terms are consistent here ($G$ is square and skew-symmetric), so no correction is needed.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 48, Theorem 5.6; p. 47, §5.8, Eq. (32) and the definitions of F_i = 2L_iR_i, L, R; p. 48, definition of 𝒮

import Mathlib
import Definitions.Def_RobustSDP_Structured_Model

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Structured

/-- Theorem 5.6, p. 48 (§5.8, error-in-variables RSDPs). Let `F(x) = F₀ + ∑ xᵢFᵢ` with symmetric
`n × n` coefficients, and for `i = 1, …, m` write `Fᵢ = 2 LᵢRᵢ` with `Lᵢ, Rᵢᵀ ∈ ℝ^{n×rᵢ}`,
`rᵢ = rank Fᵢ`; put `L = [L₁ … L_m]`, `R = [R₁; …; R_m]` and let `𝒮` be the block-diagonal
matrices `diag(S₁, …, S_m)`, `Sᵢ ∈ ℝ^{rᵢ×rᵢ}`. If `x_feas` satisfies, for some `λ ≥ 0`,
`S = Sᵀ ∈ 𝒮` and `G = −Gᵀ ∈ 𝒮`,
`[[F(x_feas) − λI − LSLᵀ, (1/2)Rᵀ + LG], [(1/2)R − GLᵀ, S]] ≻ 0`,
then every integer vector `z` closest to `x_feas` in the maximum norm satisfies `F(z) ⪰ 0`
(is feasible for (32)). -/
theorem theorem_5_6 {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (hFs : ∀ i, (Fs i).IsSymm) (r : Fin m → ℕ)
    (Ls : (i : Fin m) → Matrix (Fin n) (Fin (r i)) ℝ)
    (Rs : (i : Fin m) → Matrix (Fin (r i)) (Fin n) ℝ)
    (hFLR : ∀ i : Fin m, Fs i.succ = (2 : ℝ) • (Ls i * Rs i))
    (hrank : ∀ i : Fin m, (Fs i.succ).rank = r i)
    (xfeas : Fin m → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (Sb Gb : (i : Fin m) → Matrix (Fin (r i)) (Fin (r i)) ℝ)
    (hS : (blockDiagonal' Sb).IsSymm) (hG : (blockDiagonal' Gb)ᵀ = -blockDiagonal' Gb)
    (hLMI : (fromBlocks
      (affineMap Fs xfeas - lam • (1 : Matrix (Fin n) (Fin n) ℝ) -
        blockRow Ls * blockDiagonal' Sb * (blockRow Ls)ᵀ)
      ((1 / 2 : ℝ) • (blockCol Rs)ᵀ + blockRow Ls * blockDiagonal' Gb)
      ((1 / 2 : ℝ) • blockCol Rs - blockDiagonal' Gb * (blockRow Ls)ᵀ)
      (blockDiagonal' Sb)).PosDef) :
    ∀ z : Fin m → ℤ,
      (∀ z' : Fin m → ℤ,
        ‖(fun i => (z i : ℝ)) - xfeas‖ ≤ ‖(fun i => (z' i : ℝ)) - xfeas‖) →
      (affineMap Fs (fun i => (z i : ℝ))).PosSemidef := by sorry

end RobustSDP.Structured
