-- Prove2me | Theorems.Thm_QuadMatIneq_Basic_eq_3_2
-- name    : QuadMatIneq.Basic.eq_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:12.054255+00:00
-- url     : https://prove2.me/theorems/8712d4d2-edb7-4556-94ce-a7d648a9f58a
-- title:
--   (3.2), p. 6 — for Π ∈ 𝕊^{q+r} with Π₂₂ ⩽ 0: ker Π₂₂ ⊆ ker Π₁₂ ⟺ Π₁₂Π₂₂Π₂₂† = Π₁₂, and then Π factors through diag(Π|Π₂₂, Π₂₂)
-- statement:
--   Let $\Pi \in \mathbb{S}^{q+r}$ be symmetric, partitioned with $\Pi_{11}$ of size $q\times q$ and $\Pi_{22}$ of size $r\times r$, and suppose $\Pi_{22} \le 0$. Write $\Pi_{22}^\dagger$ for the Moore–Penrose pseudo-inverse and $\Pi\,|\,\Pi_{22} = \Pi_{11} - \Pi_{12}\Pi_{22}^\dagger\Pi_{21}$ for the generalized Schur complement. Then:
--
--   1. $\ker\Pi_{22} \subseteq \ker\Pi_{12}$ holds if and only if $\Pi_{12}\Pi_{22}\Pi_{22}^\dagger = \Pi_{12}$;
--   2. if $\ker\Pi_{22} \subseteq \ker\Pi_{12}$, then
--   $$\begin{bmatrix}\Pi_{11} & \Pi_{12}\\ \Pi_{21} & \Pi_{22}\end{bmatrix} = \begin{bmatrix} I_q & \Pi_{12}\Pi_{22}^\dagger \\ 0 & I_r\end{bmatrix}\begin{bmatrix}\Pi\,|\,\Pi_{22} & 0\\ 0 & \Pi_{22}\end{bmatrix}\begin{bmatrix} I_q & 0\\ \Pi_{22}^\dagger\Pi_{21} & I_r\end{bmatrix}.$$
--
--   This block factorization is the generalized Schur complement identity on which all of §3 rests: it reduces questions about the QMI defined by $\Pi$ to questions about the two diagonal blocks.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §3, display (3.2) and the sentence before it, p. 6

import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI

namespace QuadMatIneq.Basic
open Matrix
theorem eq_3_2 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : P.IsHermitian) (h22 : (-P.toBlocks₂₂).PosSemidef) :
    ((∀ v : κ → ℝ, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0) ↔
        P.toBlocks₁₂ * P.toBlocks₂₂ * pinv P.toBlocks₂₂ = P.toBlocks₁₂) ∧
    ((∀ v : κ → ℝ, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0) →
      P = Matrix.fromBlocks 1 (P.toBlocks₁₂ * pinv P.toBlocks₂₂) 0 1 *
            Matrix.fromBlocks (schur P) 0 0 P.toBlocks₂₂ *
            Matrix.fromBlocks 1 0 (pinv P.toBlocks₂₂ * P.toBlocks₂₁) 1) := by sorry
end QuadMatIneq.Basic
