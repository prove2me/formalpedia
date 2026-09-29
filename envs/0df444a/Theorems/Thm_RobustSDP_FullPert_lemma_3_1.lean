-- Prove2me | Theorems.Thm_RobustSDP_FullPert_lemma_3_1
-- name    : RobustSDP.FullPert.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:59:21.11372+00:00
-- url     : https://prove2.me/theorems/d264e467-1835-4f2c-8bc8-b4f83005c17c
-- title:
--   Lemma 3.1 — Robust LMI under a full norm-bounded LFR perturbation
-- statement:
--   Let $F = F^T \in \mathbb{R}^{n\times n}$, $L \in \mathbb{R}^{n\times p}$, $R \in \mathbb{R}^{q\times n}$ and $D \in \mathbb{R}^{q\times p}$ be real matrices with $q \ge 1$ and $L \neq 0$. Write $\|\cdot\|$ for the largest singular value and $X \succeq 0$ for "$X$ is symmetric positive semidefinite". Then the following are equivalent:
--
--   1. for every $\Delta \in \mathbb{R}^{p\times q}$ with $\|\Delta\| \le 1$, $\det(I - D\Delta) \neq 0$ and
--   $$F + L\Delta(I - D\Delta)^{-1}R + R^T(I - D\Delta)^{-T}\Delta^T L^T \succeq 0; \qquad (8)$$
--   2. $\|D\| < 1$ and there exists a scalar $\tau$ such that
--   $$\begin{bmatrix} F - \tau LL^T & R^T - \tau LD^T \\ R - \tau DL^T & \tau(I - DD^T)\end{bmatrix} \succeq 0. \qquad (9)$$
--
--   The lemma turns a matrix inequality required for a continuum of perturbations into a single linear matrix inequality in one extra scalar variable. It is the exact (lossless) robust counterpart of an LMI under a full, norm-bounded, linear-fractional perturbation, and Theorem 3.1 is obtained from it by rescaling.
--
--   **Formalization Note** The hypothesis $L \neq 0$ is **added**: the printed statement fails for $L = 0$ (counterexample $n = p = q = 1$, $F = 0$, $L = 0$, $D = 0$, $R = 1$: the perturbation does not enter, so condition 1 holds, while (9) reads $\begin{bmatrix}0 & 1\\ 1 & \tau\end{bmatrix} \succeq 0$, which no $\tau$ satisfies). The hypothesis $q \ge 1$ makes the paper's "matrices of appropriate size" explicit; for $q = 0$ the lower-right block is empty and the statement fails. As printed, $\tau$ carries no sign constraint. $(I - D\Delta)^{-T}$ is the transpose of the inverse.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 36, Lemma 3.1, Eq. (8) and Eq. (9)

import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.FullPert

/-- Lemma 3.1, p. 36, with the hypothesis `L ≠ 0` added (the printed statement fails for
`L = 0`: take `n = p = q = 1`, `F = 0`, `L = 0`, `D = 0`, `R = 1`; then (8) holds but (9) is
`[[0, 1], [1, τ]] ⪰ 0`, which no `τ` satisfies) and `0 < q` made explicit ("matrices of
appropriate size"). For `F = Fᵀ`: `det (I − DΔ) ≠ 0` and
`F + LΔ(I − DΔ)⁻¹R + Rᵀ(I − DΔ)⁻ᵀΔᵀLᵀ ⪰ 0` for every `Δ` with `‖Δ‖ ≤ 1` (8) iff `‖D‖ < 1` and
some scalar `τ` makes the block matrix (9) positive semidefinite. -/
theorem lemma_3_1 {n p q : ℕ} (hq : 0 < q) (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (L : Matrix (Fin n) (Fin p) ℝ) (R : Matrix (Fin q) (Fin n) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (hL : L ≠ 0) :
    (∀ Δ : Matrix (Fin p) (Fin q) ℝ, ‖Δ‖ ≤ 1 →
        (1 - D * Δ).det ≠ 0 ∧
          (F + L * Δ * (1 - D * Δ)⁻¹ * R + Rᵀ * ((1 - D * Δ)⁻¹)ᵀ * Δᵀ * Lᵀ).PosSemidef) ↔
      (‖D‖ < 1 ∧ ∃ τ : ℝ,
        (fromBlocks (F - τ • (L * Lᵀ)) (Rᵀ - τ • (L * Dᵀ)) (R - τ • (D * Lᵀ))
          (τ • (1 - D * Dᵀ))).PosSemidef) := by sorry

end RobustSDP.FullPert
