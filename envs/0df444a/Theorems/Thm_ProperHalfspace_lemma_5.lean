-- Prove2me | Theorems.Thm_ProperHalfspace_lemma_5
-- name    : ProperHalfspace.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:03:55.948658+00:00
-- url     : https://prove2.me/theorems/dde3f026-682f-48c6-afe1-74c972d921ce
-- title:
--   Lemma 5 — projection cost from the Gaussian Poincaré inequality
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R$ be smooth, with $F$ and $\|\nabla F\|_2$ square-integrable under $N(0,I_n)$. Let $E\subseteq\mathbb R^n$ be a subspace and $h_G(x)=\operatorname{sign}(w\cdot x-\theta)$, with expectations over $z\sim N(0,I_n)$.
--
--   1. If $\Pi_{E^\perp}w\ne0$, set $v=\Pi_{E^\perp}w/\|\Pi_{E^\perp}w\|_2$. Then
--   $$\bigl|\mathbf E[F(z)h_G(z)]-\mathbf E[F(z)A_Eh_G(z)]\bigr|\le\mathbf E\bigl[(v\cdot\nabla F(z))^2\bigr]^{1/2}.$$
--   2. If $\Pi_{E^\perp}w=0$, the two correlations are equal.
--
--   This bounds the cost of projecting a halfspace using only the derivative of $F$ in the direction removed from its normal.
--
--   Differences from the source: none.
-- source:
--   De, Mossel, Nadimpalli, Neeman, Efficient Proper Agnostic Learning of Halfspaces, arXiv:2611.02344 (Nov. 1, 2026), Lemma 5, p.14

import Mathlib
import Definitions.Def_ProperHalfspace_Gaussian

open MeasureTheory
open scoped ContDiff Gradient

namespace ProperHalfspace

/-- Lemma 5, p.14. De, Mossel, Nadimpalli, Neeman, arXiv:2611.02344 (Nov. 1, 2026).
For smooth `F` with `F` and `‖∇F‖₂` square-integrable under `N(0, I_n)`, a subspace `E` and `h_G(x) = sign(w · x − θ)`: if
`Π_{E⊥} w ≠ 0` and `v = Π_{E⊥} w / ‖Π_{E⊥} w‖₂` then `|E[F h_G] − E[F A_E h_G]| ≤ E[(v · ∇F)²]^{1/2}`, and if `Π_{E⊥} w = 0` the two
correlations are equal.

**Formalization Note.** `F`'s square integrability is `MemLp F 2`; `F h_G` and `F A_E h_G` are then integrable, because `h_G`
and `A_E h_G` are bounded and measurable. -/
theorem lemma_5 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hF2 : MemLp F 2 (stdGauss n)) (hgrad : MemLp (fun z => ‖∇ F z‖) 2 (stdGauss n))
    (E : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ) :
    (Eᗮ.starProjection w ≠ 0 →
      |∫ z, F z * ltfG (⇑w) θ z ∂stdGauss n - ∫ z, F z * avgOp E (ltfG (⇑w) θ) z ∂stdGauss n| ≤
        Real.sqrt (∫ z, (inner ℝ ((‖Eᗮ.starProjection w‖)⁻¹ • Eᗮ.starProjection w) (∇ F z)) ^ 2
          ∂stdGauss n)) ∧
    (Eᗮ.starProjection w = 0 →
      ∫ z, F z * ltfG (⇑w) θ z ∂stdGauss n = ∫ z, F z * avgOp E (ltfG (⇑w) θ) z ∂stdGauss n) := by sorry

end ProperHalfspace
