-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_oscillator_gibbs_exact
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.oscillator_gibbs_exact
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:14:39.253783+00:00
-- url     : https://prove2.me/theorems/f82baa15-7dc0-43a0-9c05-a1e00557bf4c
-- title:
--   Example 10 (exact oscillator Gibbs formulas)
-- statement:
--   Let $H=N+\tfrac12$ on one-mode Fock space, with simple spectrum $n+\tfrac12$ for $n\ge0$. For $E>\tfrac12$, let $\beta(E)$ be the solution of the Gibbs energy equation and $\gamma(E)=e^{-\beta(E)H}/\operatorname{Tr}e^{-\beta(E)H}$. Then
--
--   $$\beta(E)=-\log\frac{2E-1}{2E+1},\qquad S(\gamma(E))=\log\frac{\sqrt{4E^2-1}}2-E\log\frac{2E-1}{2E+1}.$$
--
--   Moreover $\beta(E)=E^{-1}+O(E^{-3})$ and $S(\gamma(E))/\log E\to1$ as $E\to\infty$. The state is the actual normalized spectral Gibbs density. This explicit model checks the constants and scaling of the general high-energy results.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 37, Example 10 (exact oscillator Gibbs formulas)

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

/-- Example 10, PDF p.37: exact oscillator Gibbs formulas, cubic-order beta
remainder, and logarithmic entropy asymptotic. The exact entropy's radical has
sqrt(4E^2-1)/2, as verified against the printed PDF. -/
theorem oscillator_gibbs_exact :
    (∀ E : ℝ, 1 / 2 < E →
      IsEquilibrium oscillatorHamiltonian E (betaAtEnergy oscillatorHamiltonian E) ∧
      IsDensity (gibbsCoefficients oscillatorHamiltonian E) ∧
      betaAtEnergy oscillatorHamiltonian E = -Real.log ((2 * E - 1) / (2 * E + 1)) ∧
      equilibriumEntropyNats oscillatorHamiltonian E =
        Real.log (Real.sqrt (4 * E ^ 2 - 1) / 2) -
          E * Real.log ((2 * E - 1) / (2 * E + 1))) ∧
    Asymptotics.IsBigO atTop
      (fun E : ℝ => betaAtEnergy oscillatorHamiltonian E - 1 / E)
      (fun E : ℝ => 1 / E ^ 3) ∧
    Tendsto (fun E => equilibriumEntropyNats oscillatorHamiltonian E / Real.log E)
      atTop (𝓝 (1 : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
