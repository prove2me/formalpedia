-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P24_decoherence_nonnegative
-- name    : QAlgorithms.Papers.Independent.Intake100.P24.decoherence_nonnegative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:13:31.125978+00:00
-- url     : https://prove2.me/theorems/e3d22664-f7ff-404e-94d6-8fc433f18e8e
-- title:
--   Finite-rate scattering has nonnegative decoherence
-- statement:
--   Let $H$ be a complex Hilbert space, $v\in H$ a unit mode vector, and $U_\omega$ unitary scattering operators with a finite positive measure $\mu$. Assume the displayed scalar integrand is integrable. Independently, let $\nu$ be a finite positive measure supported on two-dimensional unitary matrices, and set $B=\int(I-V)\,d\nu(V)$. Then
--
--   $$\operatorname{Re}\int(1-\langle v,U_\omega v\rangle)\,d\mu(\omega)\ge0,\qquad B=i\Delta+\Gamma_{\mathrm{dec}},\quad\Delta=\Delta^\dagger,\quad\Gamma_{\mathrm{dec}}\ge0,$$
--
--   where $\Delta=(B-B^\dagger)/(2i)$ and $\Gamma_{\mathrm{dec}}=(B+B^\dagger)/2$. These are the scalar rate (43) and operator decomposition (49), independent of the proposed thermal-mode decoupling.
-- source:
--   Quantum features of macroscopic fields. Entropy and dynamics, arXiv:1904.06170v1, PDF p. 8, §VI.A–B, (43),(49): nonnegative decoherence

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P24

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder Matrix.Norms.L2Operator

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

open QAlgorithms.Papers.Independent.Information100.P30 (IsPositiveMap)

namespace QAlgorithms.Papers.Independent.Intake100.P24

local instance : MeasurableSpace PolarizationMatrix := borel PolarizationMatrix

local instance : BorelSpace PolarizationMatrix := ⟨rfl⟩

/-- arXiv:1904.06170v1 PDF pp.7–8, (43),(49): scalar and operator
decoherence are nonnegative for finite-rate positive scattering measures.
The scalar statement allows an arbitrary Hilbert space and requires its unit mode
vector. The explicit integrability guard prevents a totalized divergent integral.
The operator statement includes the Hermitian shift and the decomposition (49). -/
theorem decoherence_nonnegative
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsFiniteMeasure mu]
    (U : Omega → H ≃ₗᵢ[ℂ] H) (v : H) (hv : ‖v‖ = 1)
    (hint : Integrable (fun w => (1 : ℂ) - inner ℂ v (U w v)) mu)
    (nu : Measure PolarizationMatrix) [IsFiniteMeasure nu]
    (hunit : ∀ᵐ V ∂nu, IsScatteringUnitary V) :
    0 ≤ (∫ w, (1 : ℂ) - inner ℂ v (U w v) ∂mu).re ∧
      let B : PolarizationMatrix := ∫ V, (1 : PolarizationMatrix) - V ∂nu
      (frequencyShift B).IsHermitian ∧ (decoherencePart B).PosSemidef ∧
        B = Complex.I • frequencyShift B + decoherencePart B := by sorry

end QAlgorithms.Papers.Independent.Intake100.P24

end
