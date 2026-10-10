-- Prove2me | Theorems.Thm_QuadMatIneq_Reduced_theorem_3_4
-- name    : QuadMatIneq.Reduced.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:58:56.839206+00:00
-- url     : https://prove2.me/theorems/45f7ddd5-4ac5-4436-a203-a01cfee4b2ad
-- title:
--   Theorem 3.4, p. 8 — 𝒵_r(Π)W ⊆ 𝒵_r(Π_W), with equality if W has full column rank or Π₂₂ is nonsingular
-- statement:
--   Let $\Pi\in\boldsymbol\Pi_{q,r}$ and $W\in\mathbb R^{q\times p}$. Then
--   $$\mathcal Z_r(\Pi)\,W\subseteq\mathcal Z_r(\Pi_W).$$
--   If, in addition, either $W$ has full column rank or $\Pi_{22}$ is nonsingular, then
--   $$\mathcal Z_r(\Pi)\,W = \mathcal Z_r(\Pi_W).$$
--
--   Here $\mathcal Z_r(\Pi)W = \{ZW : Z\in\mathcal Z_r(\Pi)\}$ and $\Pi_W$ is defined in (3.9). The theorem identifies the image of a QMI solution set under a linear map as the solution set of another QMI; in Section 5.2 it separates the computation of the Lyapunov matrix from that of the controller.
--
--   **Formalization Note** "$W$ has full column rank" is `W.rank = p`; "$\Pi_{22}$ nonsingular" is `IsUnit Π₂₂`.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 3.4, p. 8

import Mathlib
import Definitions.Def_QuadMatIneq_Reduced_QMI
open Matrix
open scoped MatrixOrder

namespace QuadMatIneq.Reduced

theorem theorem_3_4 {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (W : Matrix ι ρ ℝ) (hP : InPi P) :
    setMul (ZSet P) W ⊆ ZSet (PiW P W) ∧
    (W.rank = Fintype.card ρ ∨ IsUnit P.toBlocks₂₂ →
      setMul (ZSet P) W = ZSet (PiW P W)) := by sorry

end QuadMatIneq.Reduced
