-- Prove2me | Theorems.Thm_QuadMatIneq_Basic_eq_3_4
-- name    : QuadMatIneq.Basic.eq_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:59.810342+00:00
-- url     : https://prove2.me/theorems/ce3df637-f2d5-4a5a-8165-fbaa98577af1
-- title:
--   (3.4), p. 6 — Π|Π₂₂ = [I; −Π₂₂†Π₂₁]ᵀΠ[I; −Π₂₂†Π₂₁] ⩾ [I; Z]ᵀΠ[I; Z] for every Z
-- statement:
--   Let $\Pi \in \mathbb{S}^{q+r}$ be symmetric, partitioned with $\Pi_{11}$ of size $q\times q$ and $\Pi_{22}$ of size $r\times r$, and suppose $\Pi_{22} \le 0$ and $\ker\Pi_{22}\subseteq\ker\Pi_{12}$. Then
--   $$\Pi\,|\,\Pi_{22} = \begin{bmatrix} I_q \\ -\Pi_{22}^\dagger\Pi_{21}\end{bmatrix}^\top \Pi \begin{bmatrix} I_q \\ -\Pi_{22}^\dagger\Pi_{21}\end{bmatrix} \;\ge\; \begin{bmatrix} I_q \\ Z\end{bmatrix}^\top \Pi \begin{bmatrix} I_q \\ Z\end{bmatrix}\qquad\text{for every } Z \in \mathbb{R}^{r\times q},$$
--   where $\ge$ is the Loewner order ($A \ge B$ means $A - B$ is positive semidefinite), $\Pi_{22}^\dagger$ is the Moore–Penrose pseudo-inverse and $\Pi\,|\,\Pi_{22} = \Pi_{11} - \Pi_{12}\Pi_{22}^\dagger\Pi_{21}$.
--
--   So the quadratic matrix function $Z \mapsto [I;Z]^\top\Pi[I;Z]$ has a greatest element in the Loewner order, the generalized Schur complement, attained at $Z = -\Pi_{22}^\dagger\Pi_{21}$.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, §3, display (3.4), p. 6

import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI

namespace QuadMatIneq.Basic
open Matrix
theorem eq_3_4 {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : P.IsHermitian) (h22 : (-P.toBlocks₂₂).PosSemidef)
    (hker : ∀ v : κ → ℝ, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0) :
    schur P = qmiForm P (-(pinv P.toBlocks₂₂ * P.toBlocks₂₁)) ∧
      ∀ Z : Matrix κ ι ℝ, (schur P - qmiForm P Z).PosSemidef := by sorry
end QuadMatIneq.Basic
