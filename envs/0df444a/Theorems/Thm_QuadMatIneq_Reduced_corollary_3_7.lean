-- Prove2me | Theorems.Thm_QuadMatIneq_Reduced_corollary_3_7
-- name    : QuadMatIneq.Reduced.corollary_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T21:00:40.522332+00:00
-- url     : https://prove2.me/theorems/acd7ae2d-c3cb-46f9-85da-ebab6d5e644b
-- title:
--   Corollary 3.7, p. 9 — some Z ∈ 𝒵_r^+(Π) has ZW = Y iff Π|Π₂₂ > 0 and Y ∈ 𝒵_r^+(Π_W), for W of full column rank
-- statement:
--   Let $\Pi\in\mathbb S^{q+r}$ with $\Pi_{22}\le 0$ and $\ker\Pi_{22}\subseteq\ker\Pi_{12}$. Consider $W\in\mathbb R^{q\times p}$ of full column rank and $Y\in\mathbb R^{r\times p}$. Then
--   $$\exists\, Z\in\mathcal Z_r^+(\Pi)\ \text{with}\ ZW = Y\iff \Pi\,|\,\Pi_{22}>0\ \text{and}\ Y\in\mathcal Z_r^+(\Pi_W).$$
--
--   This strict version of Corollary 3.6 is closely related to the elimination lemma of robust control.
--
--   **Formalization Note** As in Corollary 3.6, the printed hypothesis $\ker\Pi_{22}\subseteq\ker\Pi_{21}$ is dimensionally impossible and is read as $\ker\Pi_{22}\subseteq\ker\Pi_{12}$.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Corollary 3.7, p. 9 (kernel condition corrected, see Formalization Note)

import Mathlib
import Definitions.Def_QuadMatIneq_Reduced_QMI
open Matrix
open scoped MatrixOrder

namespace QuadMatIneq.Reduced

theorem corollary_3_7 {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hsym : P.IsHermitian)
    (h22 : (-P.toBlocks₂₂).PosSemidef)
    (hker : ∀ v, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0)
    (W : Matrix ι ρ ℝ) (Y : Matrix κ ρ ℝ) (hW : W.rank = Fintype.card ρ) :
    (∃ Z ∈ ZPlus P, Z * W = Y) ↔ (schur P).PosDef ∧ Y ∈ ZPlus (PiW P W) := by sorry

end QuadMatIneq.Reduced
