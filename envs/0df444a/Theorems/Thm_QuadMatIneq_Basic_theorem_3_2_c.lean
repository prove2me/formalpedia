-- Prove2me | Theorems.Thm_QuadMatIneq_Basic_theorem_3_2_c
-- name    : QuadMatIneq.Basic.theorem_3_2_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:05.198342+00:00
-- url     : https://prove2.me/theorems/2211a1d8-3d2d-4f3a-a72d-87dde7b2bd63
-- title:
--   Theorem 3.2(c), p. 7 — for Π ∈ 𝚷_{q,r}, 𝒵_r(Π) has nonempty interior iff Π₂₂ = 0 or Π|Π₂₂ > 0
-- statement:
--   Let $\Pi \in \boldsymbol\Pi_{q,r}$, that is, $\Pi \in \mathbb S^{q+r}$ is symmetric with $\Pi_{22}\le 0$, $\Pi\,|\,\Pi_{22}\ge 0$ and $\ker\Pi_{22}\subseteq\ker\Pi_{12}$. Then the solution set
--   $$\mathcal Z_r(\Pi) = \Big\{ Z \in \mathbb{R}^{r\times q} : \begin{bmatrix} I_q \\ Z\end{bmatrix}^\top \Pi \begin{bmatrix} I_q \\ Z\end{bmatrix} \ge 0\Big\}$$
--   has nonempty interior in $\mathbb R^{r \times q}$ if and only if
--   $$\Pi_{22} = 0 \quad\text{or}\quad \Pi\,|\,\Pi_{22} > 0 .$$
--
--   This part makes the existence of interior points, a Slater-type property of the solution set, checkable on the blocks of $\Pi$.
--
--   **Formalization Note.** The interior is taken in $\mathbb R^{r\times q}$ with its Euclidean (product) topology, not relative to an affine hull.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 3.2(c), p. 7

import Mathlib
import Definitions.Def_QuadMatIneq_Basic_QMI

namespace QuadMatIneq.Basic
open Matrix
theorem theorem_3_2_c {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hP : InPi P) :
    (interior (ZSet P)).Nonempty ↔ P.toBlocks₂₂ = 0 ∨ (schur P).PosDef := by sorry
end QuadMatIneq.Basic
