-- Prove2me | Theorems.Thm_QuadMatIneq_Finsler_eq_4_6
-- name    : QuadMatIneq.Finsler.eq_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:48.27058+00:00
-- url     : https://prove2.me/theorems/b46b4f0b-b611-43f5-bf29-fa8d7632a029
-- title:
--   §4.3, proof of Theorem 4.8, p. 12, (4.6) — the congruence $T^\top(M-\alpha N)T$ with $T=[I\ 0;\ -N_{22}^\dagger N_{21}\ I]$
-- statement:
--   Let $M\in\mathbb S^{q+r}$ and $N\in\boldsymbol\Pi_{q,r}$ be partitioned as in (4.1), with $N\,|\,N_{22}=0$, and let $\Theta$ be as in (4.4) and
--   $$T:=\begin{bmatrix}I&0\\ -N_{22}^\dagger N_{21}&I\end{bmatrix}.$$
--   Then
--   $$T^\top NT=\begin{bmatrix}0&0\\ 0&N_{22}\end{bmatrix},\qquad T^\top MT=\begin{bmatrix}\Theta&M_{12}-N_{12}N_{22}^\dagger M_{22}\\ M_{21}-M_{22}N_{22}^\dagger N_{21}&M_{22}\end{bmatrix},$$
--   and consequently, for every $\alpha\in\mathbb R$,
--   $$T^\top(M-\alpha N)T=\begin{bmatrix}\Theta&M_{12}-N_{12}N_{22}^\dagger M_{22}\\ M_{21}-M_{22}N_{22}^\dagger N_{21}&M_{22}-\alpha N_{22}\end{bmatrix}.\qquad(4.6)$$
--
--   Since $T$ is nonsingular, (4.6) turns the condition $M-\alpha N\geqslant0$ into a condition on a block matrix whose only $\alpha$-dependence is in the lower-right block.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §4.3, proof of Theorem 4.8, p. 12, definition of T, the displays of TᵀNT and TᵀMT, and (4.6)

import Mathlib
import Definitions.Def_QuadMatIneq_Finsler_QMI

namespace QuadMatIneq.Finsler
open Matrix QuadMatIneq.Basic
theorem eq_4_6 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hMh : M.IsHermitian) (hN : InPi N) (hNs : schur N = 0) :
    (Tmat N)ᵀ * N * Tmat N = Matrix.fromBlocks 0 0 0 N.toBlocks₂₂ ∧
    (Tmat N)ᵀ * M * Tmat N =
      Matrix.fromBlocks (Theta M N)
        (M.toBlocks₁₂ - N.toBlocks₁₂ * pinv N.toBlocks₂₂ * M.toBlocks₂₂)
        (M.toBlocks₂₁ - M.toBlocks₂₂ * pinv N.toBlocks₂₂ * N.toBlocks₂₁)
        M.toBlocks₂₂ ∧
    ∀ α : ℝ, (Tmat N)ᵀ * (M - α • N) * Tmat N =
      Matrix.fromBlocks (Theta M N)
        (M.toBlocks₁₂ - N.toBlocks₁₂ * pinv N.toBlocks₂₂ * M.toBlocks₂₂)
        (M.toBlocks₂₁ - M.toBlocks₂₂ * pinv N.toBlocks₂₂ * N.toBlocks₂₁)
        (M.toBlocks₂₂ - α • N.toBlocks₂₂) := by sorry
end QuadMatIneq.Finsler
