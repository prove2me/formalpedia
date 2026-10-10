-- Prove2me | Theorems.Thm_QuadMatIneq_Basic_eq_3_3
-- name    : QuadMatIneq.Basic.eq_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:59.573757+00:00
-- url     : https://prove2.me/theorems/cae4dcaf-d619-40ab-811e-030c9fd37e79
-- title:
--   (3.3), p. 6 — completed square: [I; Z]ᵀΠ[I; Z] = Π|Π₂₂ + (Z + Π₂₂†Π₂₁)ᵀ Π₂₂ (Z + Π₂₂†Π₂₁)
-- statement:
--   Let $\Pi \in \mathbb{S}^{q+r}$ be symmetric, partitioned with $\Pi_{11}$ of size $q\times q$ and $\Pi_{22}$ of size $r\times r$, and suppose $\Pi_{22} \le 0$ and $\ker\Pi_{22}\subseteq\ker\Pi_{12}$. Then for every $Z \in \mathbb{R}^{r\times q}$,
--   $$\begin{bmatrix} I_q \\ Z\end{bmatrix}^\top \begin{bmatrix}\Pi_{11} & \Pi_{12}\\ \Pi_{21} & \Pi_{22}\end{bmatrix} \begin{bmatrix} I_q \\ Z\end{bmatrix} = \Pi\,|\,\Pi_{22} + (Z + \Pi_{22}^\dagger\Pi_{21})^\top\,\Pi_{22}\,(Z + \Pi_{22}^\dagger\Pi_{21}),$$
--   where $\Pi_{22}^\dagger$ is the Moore–Penrose pseudo-inverse and $\Pi\,|\,\Pi_{22} = \Pi_{11} - \Pi_{12}\Pi_{22}^\dagger\Pi_{21}$.
--
--   This "completion of the square" writes the quadratic matrix function as a constant plus a negative semidefinite quadratic term centred at $-\Pi_{22}^\dagger\Pi_{21}$, and is used in every part of Theorem 3.2.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §3, display (3.3), p. 6

import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI

namespace QuadMatIneq.Basic
open Matrix
theorem eq_3_3 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : P.IsHermitian) (h22 : (-P.toBlocks₂₂).PosSemidef)
    (hker : ∀ v : κ → ℝ, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0) (Z : Matrix κ ι ℝ) :
    qmiForm P Z = schur P +
      (Z + pinv P.toBlocks₂₂ * P.toBlocks₂₁)ᵀ * P.toBlocks₂₂ *
        (Z + pinv P.toBlocks₂₂ * P.toBlocks₂₁) := by sorry
end QuadMatIneq.Basic
