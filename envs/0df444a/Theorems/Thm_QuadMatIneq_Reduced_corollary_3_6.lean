-- Prove2me | Theorems.Thm_QuadMatIneq_Reduced_corollary_3_6
-- name    : QuadMatIneq.Reduced.corollary_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:59:19.483476+00:00
-- url     : https://prove2.me/theorems/cd519511-b11a-4a0b-9b8f-c3546ed79af6
-- title:
--   Corollary 3.6, p. 9 — some Z ∈ 𝒵_r(Π) has ZW = Y iff Π ∈ 𝚷_{q,r} and Y ∈ 𝒵_r(Π_W)
-- statement:
--   Let $\Pi\in\mathbb S^{q+r}$ with $\Pi_{22}\le 0$ and $\ker\Pi_{22}\subseteq\ker\Pi_{12}$, let $W\in\mathbb R^{q\times p}$ and $Y\in\mathbb R^{r\times p}$, and suppose that either $W$ has full column rank or $\Pi_{22}$ is nonsingular. Then
--   $$\exists\, Z\in\mathcal Z_r(\Pi)\ \text{with}\ ZW = Y \iff \Pi\in\boldsymbol\Pi_{q,r}\ \text{and}\ Y\in\mathcal Z_r(\Pi_W).$$
--
--   The corollary decides whether a QMI has a solution satisfying a prescribed linear constraint; it is how Theorem 5.3 eliminates the controller variable from the LMI of Theorem 5.1.
--
--   **Formalization Note** The paper prints the hypothesis as $\ker\Pi_{22}\subseteq\ker\Pi_{21}$, which is dimensionally impossible ($\ker\Pi_{22}\subseteq\mathbb R^r$, $\ker\Pi_{21}\subseteq\mathbb R^q$). The statement uses $\ker\Pi_{22}\subseteq\ker\Pi_{12}$, the kernel condition in the definition of $\boldsymbol\Pi_{q,r}$ that the proof requires.
-- source:
--   van Waarde–Camlibel–Eising–Trentelman, arXiv:2203.12959v3, Corollary 3.6, p. 9 (kernel condition corrected, see Formalization Note)

import Mathlib
import Definitions.Def_QuadMatIneq_Reduced_QMI
open Matrix
open scoped MatrixOrder

namespace QuadMatIneq.Reduced

theorem corollary_3_6 {ι κ ρ : Type*} [Fintype ι] [Fintype κ] [Fintype ρ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]
    (P : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) (hsym : P.IsHermitian)
    (h22 : (-P.toBlocks₂₂).PosSemidef)
    (hker : ∀ v, P.toBlocks₂₂ *ᵥ v = 0 → P.toBlocks₁₂ *ᵥ v = 0)
    (W : Matrix ι ρ ℝ) (Y : Matrix κ ρ ℝ)
    (hW : W.rank = Fintype.card ρ ∨ IsUnit P.toBlocks₂₂) :
    (∃ Z ∈ ZSet P, Z * W = Y) ↔ InPi P ∧ Y ∈ ZSet (PiW P W) := by sorry

end QuadMatIneq.Reduced
