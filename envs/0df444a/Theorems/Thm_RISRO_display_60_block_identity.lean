-- Prove2me | Theorems.Thm_RISRO_display_60_block_identity
-- name    : RISRO.display_60_block_identity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T10:31:46.609598+00:00
-- url     : https://prove2.me/theorems/1181b8ef-6d8c-4d04-821e-ed23ef8caa20
-- title:
--   Display (60) — block form of $X^{t+1}-\bar X$ (corrected: printed $V_\perp^{t\top}$ read as $V_\perp^t$)
-- statement:
--   Let $\bar X$ have rank $r$, let $U,V$ be orthonormal with orthonormal complements $U_\perp,V_\perp$, put $\tilde B=U^\top\bar XV$, $\tilde D_1=U_\perp^\top\bar XV$, $\tilde D_2^\top=U^\top\bar XV_\perp$, and let $\tilde B$ and $B\in\mathbb R^{r\times r}$ be invertible. For $D_1$, $D_2$ arbitrary, $X_U=UB+U_\perp D_1$, $X_V=VB^\top+V_\perp D_2$:
--
--   1. $\tilde D_1\tilde B^{-1}\tilde D_2^\top=U_\perp^\top\bar XV_\perp$;
--   2. $\bar X=[U\ U_\perp][U\ U_\perp]^\top\bar X[V\ V_\perp][V\ V_\perp]^\top=[U\ U_\perp]\begin{bmatrix}\tilde B&\tilde D_2^\top\\ \tilde D_1&\tilde D_1\tilde B^{-1}\tilde D_2^\top\end{bmatrix}[V\ V_\perp]^\top$;
--   3. $X_UB^{-1}X_V^\top=[U\ U_\perp]\begin{bmatrix}B&D_2^\top\\ D_1&D_1B^{-1}D_2^\top\end{bmatrix}[V\ V_\perp]^\top$;
--   4. with $\Delta=D_1B^{-1}D_2^\top-\tilde D_1\tilde B^{-1}\tilde D_2^\top$,
--
--   $$
--   \|X_UB^{-1}X_V^\top-\bar X\|_F^2=\left\|\begin{matrix}B-\tilde B&D_2^\top-\tilde D_2^\top\\ D_1-\tilde D_1&\Delta\end{matrix}\right\|_F^2 .
--   $$
--
--   This separates the error of the new iterate into the least squares errors and the Schur-complement term $\Delta$.
--
--   Differences from the source:
--   - correction: the first identity has right side U_⊥^{t⊤} X̄ V_⊥^{t⊤} → right side U_⊥ᵀ X̄ V_⊥; reason: the printed product is ill-typed, since X̄ V_⊥ᵀ has mismatched dimensions whenever 0 < r; the block forms that follow use the (2,2) block U_⊥ᵀ X̄ V_⊥
--   - generalization: the data U^t, V^t, U_⊥^t, V_⊥^t of an iteration of RISRO → any orthonormal frames with orthonormal complements; reason: the proof uses only orthonormality; every iteration of every run supplies such frames
--   - generalization: B^{t+1}, D₁^{t+1}, D₂^{t+1} the solution of (5) with B^{t+1} invertible → any B, D₁, D₂ with B invertible; reason: the four identities are algebraic and use only the invertibility of B̃ and B and rank X̄ = r; the solution of (5) is a special case
--   - encoding: block matrices and the Frobenius norm of a 2×2 block matrix → blockForm as a sum of four products, and the sum of the four squared Frobenius norms; reason: the same matrix and the same norm
-- source:
--   Luo, Huang, Li & Zhang, Recursive Importance Sketching for Rank Constrained Least Squares, arXiv:2011.08360v4, proof of Theorem 1, Step 4, display (60), p.40

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic
import Definitions.Def_RISRO_IsFrame
import Definitions.Def_RISRO_blockForm

open HighDimStat.MatrixRank Matrix IRLSM.Convergence

namespace RISRO

/-- **Step 4 of the proof of Theorem 1: the block forms and (60).** If `X̄` has rank `r` and
`B̃`, `B` are invertible, then `D̃₁ B̃⁻¹ D̃₂ᵀ = U_⊥ᵀ X̄ V_⊥`,
`X̄ = [U U_⊥] [B̃ D̃₂ᵀ; D̃₁ D̃₁ B̃⁻¹ D̃₂ᵀ] [V V_⊥]ᵀ`,
`X_U B⁻¹ X_Vᵀ = [U U_⊥] [B D₂ᵀ; D₁ D₁ B⁻¹ D₂ᵀ] [V V_⊥]ᵀ`, and (60),
`‖X^{t+1} - X̄‖_F² = ‖[B - B̃, D₂ᵀ - D̃₂ᵀ; D₁ - D̃₁, Δ]‖_F²` with
`Δ = D₁ B⁻¹ D₂ᵀ - D̃₁ B̃⁻¹ D̃₂ᵀ`. The middle equality
`X̄ = [U U_⊥][U U_⊥]ᵀ X̄ [V V_⊥][V V_⊥]ᵀ` is included.

Luo, Huang, Li & Zhang, arXiv:2011.08360v4, proof of Theorem 1, Step 4, display (60), p.40.

Formalization Notes: the page prints the first identity with right-hand side `U_⊥ᵀ X̄ V_⊥ᵀ`, which is
ill-typed; the term is `U_⊥ᵀ X̄ V_⊥`. `B̃ = Uᵀ X̄ V`, `D̃₁ = U_⊥ᵀ X̄ V`, `D̃₂ᵀ = Uᵀ X̄ V_⊥`, display (7).
`⁻¹` is the true inverse here, as `B̃` and `B` are assumed invertible. `X_U = U B + U_⊥ D₁`,
`X_V = V Bᵀ + V_⊥ D₂` (Algorithm 1, step 5). The Frobenius norm of the block matrix in (60) is the
sum of the squares of the Frobenius norms of its four blocks. -/
theorem display_60_block_identity {p₁ p₂ r : ℕ} (Xbar : Matrix (Fin p₁) (Fin p₂) ℝ)
    (U : Matrix (Fin p₁) (Fin r) ℝ) (Uc : Matrix (Fin p₁) (Fin (p₁ - r)) ℝ)
    (V : Matrix (Fin p₂) (Fin r) ℝ) (Vc : Matrix (Fin p₂) (Fin (p₂ - r)) ℝ)
    (B : Matrix (Fin r) (Fin r) ℝ) (D₁ : Matrix (Fin (p₁ - r)) (Fin r) ℝ)
    (D₂ : Matrix (Fin (p₂ - r)) (Fin r) ℝ)
    (hrank : Xbar.rank = r) (hU : IsFrame U Uc) (hV : IsFrame V Vc)
    (hBtilde : IsUnit (Uᵀ * Xbar * V).det) (hB : IsUnit B.det) :
    (Ucᵀ * Xbar * V) * (Uᵀ * Xbar * V)⁻¹ * (Uᵀ * Xbar * Vc) = Ucᵀ * Xbar * Vc ∧
      Xbar = (U * Uᵀ + Uc * Ucᵀ) * Xbar * (V * Vᵀ + Vc * Vcᵀ) ∧
      Xbar = blockForm U Uc V Vc (Uᵀ * Xbar * V) (Uᵀ * Xbar * Vc) (Ucᵀ * Xbar * V)
        ((Ucᵀ * Xbar * V) * (Uᵀ * Xbar * V)⁻¹ * (Uᵀ * Xbar * Vc)) ∧
      (U * B + Uc * D₁) * B⁻¹ * (V * Bᵀ + Vc * D₂)ᵀ =
        blockForm U Uc V Vc B D₂ᵀ D₁ (D₁ * B⁻¹ * D₂ᵀ) ∧
      frobeniusNorm ((U * B + Uc * D₁) * B⁻¹ * (V * Bᵀ + Vc * D₂)ᵀ - Xbar) ^ 2 =
        frobeniusNorm (B - Uᵀ * Xbar * V) ^ 2 + frobeniusNorm (D₂ᵀ - Uᵀ * Xbar * Vc) ^ 2 +
          frobeniusNorm (D₁ - Ucᵀ * Xbar * V) ^ 2 +
          frobeniusNorm (D₁ * B⁻¹ * D₂ᵀ - (Ucᵀ * Xbar * V) * (Uᵀ * Xbar * V)⁻¹ * (Uᵀ * Xbar * Vc)) ^ 2 := by sorry

end RISRO
