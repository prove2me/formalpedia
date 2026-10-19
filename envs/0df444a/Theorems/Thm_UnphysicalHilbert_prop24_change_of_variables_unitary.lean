-- Prove2me | Theorems.Thm_UnphysicalHilbert_prop24_change_of_variables_unitary
-- name    : UnphysicalHilbert.prop24_change_of_variables_unitary
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T21:07:32.570237+00:00
-- url     : https://prove2.me/theorems/07611fa2-fe1c-4c3b-9f06-592e1c4d95e1
-- title:
--   Proposition 24 — changes of variables induce unitaries on $L^2(\mathbb R)$
-- statement:
--   Let $f:\mathbb R\to\mathbb R$ be an orientation-preserving diffeomorphism ($f$ and $f^{-1}$ smooth, $f$ strictly increasing). Then there is a unitary operator $U$ on $L^2(\mathbb R;\mathbb C)$ (Lebesgue measure) such that for every $\psi\in L^2(\mathbb R)$,
--   $$(U\psi)(y)=\psi\bigl(f^{-1}(y)\bigr)\sqrt{\bigl|(f^{-1})'(y)\bigr|}\qquad\text{for almost every }y\in\mathbb R .$$
--
--   A change of the position coordinate is a change of representation that preserves all inner products of wave functions.
--
--   **Formalization Note** "Unitary" is encoded as a linear isometric equivalence of $L^2(\mathbb R;\mathbb C)$ onto itself, so surjectivity is part of the claim; the paper's proof checks preservation of the inner product, eq. (25). The paper writes the Jacobian as $|df^{-1}/dx|$; the formula uses the derivative of $f^{-1}$ at $y$, which is what eq. (25) requires.
-- source:
--   G. Carcassi, C. A. Aidala, F. Calderón, *The unphysicality of Hilbert spaces*, arXiv:2308.06669v3 [quant-ph], 22 Dec 2024, https://arxiv.org/abs/2308.06669, Section VI, p. 11, Proposition 24 and eq. (25)

import Definitions.Def_UnphysicalHilbert_Position

namespace UnphysicalHilbert

open MeasureTheory

/-- Proposition 24: an orientation-preserving diffeomorphism of `ℝ` induces a unitary
operator on `L²(ℝ)` via `ψ ↦ ψ(f⁻¹(y)) √|(f⁻¹)'(y)|`. -/
theorem prop24_change_of_variables_unitary (f : ℝ ≃ ℝ) (hf : IsOrientationPreservingDiffeo f) :
    ∃ U : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      ∀ ψ : Lp ℂ 2 (volume : Measure ℝ),
        (U ψ : ℝ → ℂ) =ᵐ[volume] changeOfVariables f (ψ : ℝ → ℂ) := by
  sorry

end UnphysicalHilbert
