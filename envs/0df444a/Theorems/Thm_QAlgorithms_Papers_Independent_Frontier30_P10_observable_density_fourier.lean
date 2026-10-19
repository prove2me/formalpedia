-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P10_observable_density_fourier
-- name    : QAlgorithms.Papers.Independent.Frontier30.P10.observable_density_fourier
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:15:17.544647+00:00
-- url     : https://prove2.me/theorems/ce5bd21d-081d-4d8e-96d9-402394dbcf79
-- title:
--   Weak operator density from an integrable characteristic function
-- statement:
--   Let $M$ be a normalized POVM on the standard symplectic space $Z=\mathbb R^{2n}$ acting on a nonzero separable complex Hilbert space $\mathcal H$ carrying the source’s strongly continuous irreducible Weyl system. Write $\phi_M(w)=\int_Z e^{i\Delta(w,z)}M(dz)$ for its operator characteristic function, where $\Delta(w,z)=\sum_j(w_{j,y}z_{j,x}-w_{j,x}z_{j,y})$, and let $dz$ be standard symplectic volume. If $\int_Z\|\phi_M(w)\|\,dw<\infty$ in operator norm, then $M$ has an almost everywhere defined bounded positive operator density $p_M$ with
--
--   $$
--   M(S)=\int_S p_M(z)\,dz,\qquad
--   \int_Zp_M(z)\,dz=I,\qquad
--   p_M(z)=(2\pi)^{-2n}\int_Ze^{-i\Delta(w,z)}\phi_M(w)\,dw
--   \quad\text{almost everywhere}.
--   $$
--
--   All operator identities are weak identities, tested on Hilbert vectors; each scalar Fourier integral is integrable. The density need not have integrable operator norm. This is the operator-density form of symplectic Fourier inversion.
-- source:
--   Entanglement-breaking channels in infinite dimensions, arXiv:0802.0235v1, PDF p. 8, Unnumbered: integrable characteristic function gives operator density (21)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P10

noncomputable section

open MeasureTheory

open scoped ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P10

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Holevo, arXiv:0802.0235v1, PDF p.8, (21).
Only the operator norm is assumed integrable. Density normalization and the
Fourier inverse are weak: no Bochner integral in the nonseparable operator
norm space, nor integrability of the density's operator norm, is required. -/
theorem observable_density_fourier [SecondCountableTopology H] [Nontrivial H]
    {a : ℕ} (_W : WeylSystem H a) {n : ℕ} (M : HilbertPOVM H (Phase n → ℝ)) (phi : (Phase n → ℝ) → H →L[ℂ] H)
    (hchar : HasCharacteristic M phi)
    (hint : Integrable (fun w => ‖phi w‖) (volume : Measure (Phase n → ℝ))) :
    ∃ p : (Phase n → ℝ) → H →L[ℂ] H,
      (∀ᵐ z ∂(volume : Measure (Phase n → ℝ)), ∀ u : H,
        (inner ℂ u (p z u)).im = 0 ∧ 0 ≤ (inner ℂ u (p z u)).re) ∧
      (∀ u : H, Integrable (fun z => (inner ℂ u (p z u)).re)
          (volume : Measure (Phase n → ℝ)) ∧
        (∫ z, (inner ℂ u (p z u)).re ∂(volume : Measure (Phase n → ℝ))) = ‖u‖ ^ 2 ∧
        ∀ S : Set (Phase n → ℝ), MeasurableSet S →
          M.law u S = ENNReal.ofReal
            (∫ z in S, (inner ℂ u (p z u)).re ∂(volume : Measure (Phase n → ℝ)))) ∧
      (∀ᵐ z ∂(volume : Measure (Phase n → ℝ)), ∀ u v : H,
        Integrable (fun w => fourierCharacter (-w) z * inner ℂ u (phi w v))
          (volume : Measure (Phase n → ℝ)) ∧
        inner ℂ u (p z v) =
          (((2 * Real.pi) ^ (2 * n))⁻¹ : ℝ) •
            (∫ w, fourierCharacter (-w) z * inner ℂ u (phi w v)
              ∂(volume : Measure (Phase n → ℝ)))) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P10

end
