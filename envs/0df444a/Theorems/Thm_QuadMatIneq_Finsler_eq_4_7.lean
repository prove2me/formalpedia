-- Prove2me | Theorems.Thm_QuadMatIneq_Finsler_eq_4_7
-- name    : QuadMatIneq.Finsler.eq_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:49.862023+00:00
-- url     : https://prove2.me/theorems/4466c755-9e83-4275-b68a-e41b1f9d9372
-- title:
--   §4.3, proof of Theorem 4.8, p. 12, (4.7a)–(4.7b) — $\Theta = M|M_{22} + D^\top M_{22}D$ and $M_{22}D = M_{21}-M_{22}N_{22}^\dagger N_{21}$
-- statement:
--   Let $M,N\in\mathbb S^{q+r}$ be partitioned as in (4.1), let $\Theta$ be as in (4.4), and assume $\ker M_{22}\subseteq\ker M_{12}$. Write $D:=M_{22}^\dagger M_{21}-N_{22}^\dagger N_{21}$. Then
--   $$\Theta=M\,|\,M_{22}+D^\top M_{22}\,D\qquad(4.7a)$$
--   and
--   $$M_{22}\,D=M_{21}-M_{22}N_{22}^\dagger N_{21}.\qquad(4.7b)$$
--
--   The identity (4.7a) splits $\Theta$ into the Schur complement of $M$ and a term controlled by $M_{22}$; together with (4.7b) it relates the kernel of $\Theta$ to the kernel of $M\,|\,M_{22}$.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §4.3, proof of Theorem 4.8, p. 12, (4.7a) and (4.7b)

import Mathlib
import Definitions.Def_QuadMatIneq_Finsler_QMI

namespace QuadMatIneq.Finsler
open Matrix QuadMatIneq.Basic
theorem eq_4_7 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M N : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hMh : M.IsHermitian) (hNh : N.IsHermitian)
    (hMker : ∀ v : κ → ℝ, M.toBlocks₂₂ *ᵥ v = 0 → M.toBlocks₁₂ *ᵥ v = 0) :
    Theta M N = schur M +
      (pinv M.toBlocks₂₂ * M.toBlocks₂₁ - pinv N.toBlocks₂₂ * N.toBlocks₂₁)ᵀ * M.toBlocks₂₂ *
        (pinv M.toBlocks₂₂ * M.toBlocks₂₁ - pinv N.toBlocks₂₂ * N.toBlocks₂₁) ∧
    M.toBlocks₂₂ * (pinv M.toBlocks₂₂ * M.toBlocks₂₁ - pinv N.toBlocks₂₂ * N.toBlocks₂₁) =
      M.toBlocks₂₁ - M.toBlocks₂₂ * pinv N.toBlocks₂₂ * N.toBlocks₂₁ := by sorry
end QuadMatIneq.Finsler
