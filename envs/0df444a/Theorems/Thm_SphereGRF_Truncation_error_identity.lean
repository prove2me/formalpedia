-- Prove2me | Theorems.Thm_SphereGRF_Truncation_error_identity
-- name    : SphereGRF.Truncation.error_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:59.69998+00:00
-- url     : https://prove2.me/theorems/8f71b1bd-503b-4de2-b2cb-6dd2a0d9338f
-- title:
--   §5, p. 26 — squared mean-square truncation error equals the spectral tail
-- statement:
--   Let $(A_\ell)_{\ell\ge0}$ be a nonnegative angular power spectrum for which $\sum_\ell(2\ell+1)A_\ell$ is finite. Form $T$ and $T^\kappa$ from independent standard normal coefficients as above. For every $\kappa\ge0$,
--
--   $$
--   \mathbb E\,\|T-T^\kappa\|_{L^2(S^2)}^2
--     =\sum_{\ell=\kappa+1}^{\infty}(2\ell+1)A_\ell.
--   $$
--
--   This identity identifies the exact spectral tail that controls all subsequent truncation estimates.
--
--   **Formalization Note** The displayed equation on page 26 omits the square on the norm, while its derivation and subsequent estimate use squared norms. The formal statement records the squared identity. Summability makes both sides finite. The Gaussian variables are required to be measurable, standard normal, and jointly independent.
-- source:
--   Lang, Schwab, Isotropic Gaussian random fields on the sphere, arXiv:1305.1170v3, §5, proof of Proposition 5.2, p. 26, third display (square corrected)

import Mathlib
import Definitions.Def_SphereGRF_Truncation_Setting

open MeasureTheory Filter ProbabilityTheory

namespace SphereGRF.Truncation

theorem error_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℕ → ℝ) (X : ℕ → ℕ → Fin 2 → Ω → ℝ)
    (hA0 : ∀ ℓ, 0 ≤ A ℓ)
    (hAsum : Summable (fun ℓ : ℕ => (((2 * ℓ + 1 : ℕ) : ℝ) * A ℓ)))
    (hX : IsKLInput P X)
    (κ : ℕ) :
    (∫⁻ ω, l2S2Sq (fun y => klField A X ω y - klTrunc A X κ ω y) ∂P) =
      ENNReal.ofReal (∑' ℓ : ℕ,
        if κ < ℓ then (((2 * ℓ + 1 : ℕ) : ℝ) * A ℓ) else 0) := by sorry

end SphereGRF.Truncation
