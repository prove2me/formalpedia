-- Prove2me | Theorems.Thm_QuadMatIneq_Basic_theorem_3_2_e
-- name    : QuadMatIneq.Basic.theorem_3_2_e
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:15:59.826434+00:00
-- url     : https://prove2.me/theorems/23f74b39-2316-4e08-bcb0-1267907518a7
-- title:
--   Theorem 3.2(e), p. 7 — for Π ∈ 𝚷_{q,r}, 𝒵_r^0(Π) is nonempty iff rank Π₂₂ ⩾ rank Π|Π₂₂
-- statement:
--   Let $\Pi \in \boldsymbol\Pi_{q,r}$, that is, $\Pi \in \mathbb S^{q+r}$ is symmetric with $\Pi_{22}\le 0$, $\Pi\,|\,\Pi_{22}\ge 0$ and $\ker\Pi_{22}\subseteq\ker\Pi_{12}$. Then the set of solutions of the quadratic matrix equation
--   $$\mathcal Z_r^0(\Pi) = \Big\{ Z \in \mathbb{R}^{r\times q} : \begin{bmatrix} I_q \\ Z\end{bmatrix}^\top \Pi \begin{bmatrix} I_q \\ Z\end{bmatrix} = 0\Big\}$$
--   is nonempty if and only if
--   $$\operatorname{rank}\Pi_{22} \;\ge\; \operatorname{rank}\,(\Pi\,|\,\Pi_{22}).$$
--   Here $\Pi_{22}$ is $r\times r$ and $\Pi\,|\,\Pi_{22} = \Pi_{11} - \Pi_{12}\Pi_{22}^\dagger\Pi_{21}$ is $q\times q$.
--
--   This rank condition decides when the quadratic matrix equation $[I_q;Z]^\top\Pi[I_q;Z] = 0$, the boundary case of the QMI, is solvable.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 3.2(e), p. 7

import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI

namespace QuadMatIneq.Basic
open Matrix
theorem theorem_3_2_e {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    (ZZero P).Nonempty ↔ (schur P).rank ≤ P.toBlocks₂₂.rank := by sorry
end QuadMatIneq.Basic
