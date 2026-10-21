-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P37_three_mode_normal_form
-- name    : QAlgorithms.Papers.Independent.Claimed50.P37.three_mode_normal_form
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:39:05.788205+00:00
-- url     : https://prove2.me/theorems/fef4f4ee-37d3-4e13-81a8-164a3e055b3b
-- title:
--   Pure three-mode Gaussian preparation across the two-input/one-output split
-- statement:
--   Let $\rho$ be any normalized pure Gaussian state of three full bosonic modes, split into two input modes and one output mode. Gaussian first moments are arbitrary. There exist $r\ge0$, a two-mode symplectic unitary $U_i$ on the inputs, a one-mode symplectic unitary $U_o$ on the output, and local displacements $D_i,D_o$ such that
--
--   $$
--   \rho=(D_iU_i\otimes D_oU_o)\,|\Psi_r\rangle\langle\Psi_r|\,(D_iU_i\otimes D_oU_o)^\dagger,
--   \qquad
--   |\Psi_r\rangle=\frac1{\cosh r}\sum_{k=0}^{\infty}(\tanh r)^k|k\rangle_{i_1}|0\rangle_{i_2}|k\rangle_o.
--   $$
--
--   The displayed resource is a normalized pure trace-class state. The unitaries act on complete oscillator Hilbert spaces and implement real symplectic coordinate transformations. Here locality refers to the input/output split, so $U_i$ may mix the two input modes. The value $r=0$ includes the product vacuum. This identifies the pure local resource needed for the subsequent map factorization.
-- source:
--   Gaussian transformations and distillation of entangled Gaussian states, arXiv:quant-ph/0204069v2, PDF p. 4, Eq.(11) and following normal-form assertion

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P37

noncomputable section

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P37

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass productCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (PureState rankOne)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel composeKernel)

/-- Fiurasek, arXiv:quant-ph/0204069v2, PDF pp.3–4, Eq.(11) and following
normal-form assertion: every pure three-mode Gaussian state is prepared from a
squeezed vacuum pair and a vacuum mode by a two-input symplectic unitary and a
one-output symplectic unitary. Local displacements restore the arbitrary first
moments omitted in the centered covariance discussion. The input/output split
is 2|1; the input transformation is not required to factor between its two modes. -/
theorem three_mode_normal_form
    (rho : PureState (FockLabel 2 × FockLabel 1))
    (hgaussian : IsGaussianPair rho.val.coefficients) :
    ∃ r : ℝ, 0 ≤ r ∧
      IsDensity (squeezedVacuumResource r) ∧
      (∃ u : Hilbert (FockLabel 2 × FockLabel 1),
        ‖u‖ = 1 ∧ squeezedVacuumResource r = rankOne u) ∧
      ∃ (Ui : Hilbert (FockLabel 2) ≃ₗᵢ[ℂ] Hilbert (FockLabel 2))
        (Uo : Hilbert (FockLabel 1) ≃ₗᵢ[ℂ] Hilbert (FockLabel 1))
        (di : PhaseCoordinates 2) (dout : PhaseCoordinates 1),
        IsSymplecticUnitary Ui ∧ IsSymplecticUnitary Uo ∧
        rho.val.coefficients = normalFormPreparation Ui Uo di dout r := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P37

end
