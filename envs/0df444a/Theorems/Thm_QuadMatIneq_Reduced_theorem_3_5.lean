-- Prove2me | Theorems.Thm_QuadMatIneq_Reduced_theorem_3_5
-- name    : QuadMatIneq.Reduced.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:59:04.79778+00:00
-- url     : https://prove2.me/theorems/4ada1522-20d2-41ac-9868-25a75a8798ec
-- title:
--   Theorem 3.5, p. 9 — 𝒵_r^+(Π)W = 𝒵_r^+(Π_W) for W of full column rank when 𝒵_r^+(Π) ≠ ∅
-- statement:
--   Let $\Pi\in\boldsymbol\Pi_{q,r}$ and $W\in\mathbb R^{q\times p}$. Assume that $W$ has full column rank and that $\mathcal Z_r^+(\Pi)$ is nonempty. Then
--   $$\mathcal Z_r^+(\Pi)\,W = \mathcal Z_r^+(\Pi_W).$$
--
--   This is the strict counterpart of Theorem 3.4, used for the strict LMIs of Theorem 5.3(b).
--
--   **Formalization Note** The paper only states that the proof is similar to that of Theorem 3.4; the statement is formalized as printed.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Theorem 3.5, p. 9

import Mathlib
import Definitions.Def_QuadMatIneq_Reduced_QMI
open Matrix
open scoped MatrixOrder

namespace QuadMatIneq.Reduced

theorem theorem_3_5 {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (W : Matrix ι ρ ℝ) (hP : InPi P)
    (hW : W.rank = Fintype.card ρ) (hne : (ZPlus P).Nonempty) :
    setMul (ZPlus P) W = ZPlus (PiW P W) := by sorry

end QuadMatIneq.Reduced
