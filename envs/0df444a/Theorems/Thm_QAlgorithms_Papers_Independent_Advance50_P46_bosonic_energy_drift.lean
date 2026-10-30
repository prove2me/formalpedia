-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_bosonic_energy_drift
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.bosonic_energy_drift
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:17:22.680389+00:00
-- url     : https://prove2.me/theorems/5d3c8e79-8867-43d2-8640-5db790ddf8bd
-- title:
--   Example 12, exact energy drift of attenuator/amplifier
-- statement:
--   Let $\rho_0$ be any normalized Fock-space state, $N|n\rangle=n|n\rangle$, and $M=N+I$. Use the attenuator and amplifier parameterization of PDF p.27, with amplitude factors $e^{-t/2}$ and $e^{t/2}$. For every $t\ge0$,
--
--   $$\operatorname{Tr}(N\Lambda_t^{\rm att}(\rho_0))=e^{-t}\operatorname{Tr}(N\rho_0),\qquad\operatorname{Tr}(M\Lambda_t^{\rm amp}(\rho_0))=e^t\operatorname{Tr}(M\rho_0).$$
--
--   These equalities hold in the extended nonnegative reals, including infinite initial energies. For a finite initial expectation the corresponding time derivative is respectively minus or plus the current expectation, with a right derivative at zero. No finite second moment is required. These identities supply the energy drift needed in entropy applications.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 43, Example 12, exact energy drift of attenuator/amplifier

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P46

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P46

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Bridge50.P23 (energyMagnitude numberEnergy)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize rankOne tensorApply productCoeff IsBarycenter)

attribute [local instance] Classical.propDecidable Classical.decEq

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Example 12, PDF pp.42--43: exact extended energy laws and finite-energy
right derivatives. No second moment is required. -/
theorem bosonic_energy_drift (rho : State ℕ) (t : ℝ) (ht : 0 ≤ t) :
    numberEnergy (attenuatorTimeKernel t rho.coefficients) =
      ENNReal.ofReal (Real.exp (-t)) * numberEnergy rho.coefficients ∧
    realSpectrumMeanEnergy amplifierEnergy (amplifierTimeKernel t rho.coefficients) =
      ENNReal.ofReal (Real.exp t) * realSpectrumMeanEnergy amplifierEnergy rho.coefficients ∧
    (numberEnergy rho.coefficients < ⊤ →
      HasDerivWithinAt (fun r : ℝ =>
        (numberEnergy (attenuatorTimeKernel r rho.coefficients)).toReal)
        (-(numberEnergy (attenuatorTimeKernel t rho.coefficients)).toReal) (Set.Ici 0) t) ∧
    (realSpectrumMeanEnergy amplifierEnergy rho.coefficients < ⊤ →
      HasDerivWithinAt (fun r : ℝ =>
        (realSpectrumMeanEnergy amplifierEnergy (amplifierTimeKernel r rho.coefficients)).toReal)
        ((realSpectrumMeanEnergy amplifierEnergy (amplifierTimeKernel t rho.coefficients)).toReal) (Set.Ici 0) t) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
