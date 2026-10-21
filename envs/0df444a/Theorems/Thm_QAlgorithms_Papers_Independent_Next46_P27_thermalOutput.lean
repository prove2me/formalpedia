-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P27_thermalOutput
-- name    : QAlgorithms.Papers.Independent.Next46.P27.thermalOutput
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:26:05.255712+00:00
-- url     : https://prove2.me/theorems/beb8a81c-55ba-4150-ac53-9f5fcc4c5b88
-- title:
--   Gaussian noise propagates Gibbs inputs to Gibbs outputs
-- statement:
--   Let $\beta>0$, let $v\ge0$, and put $M=(e^\beta-1)^{-1}$. Define $\beta_{\rm out}=\log(1+(M+v)^{-1})$. On the full Fock space, the normalized Gibbs operators have matrix entries
--
--   $$\langle m|\rho_\beta|n\rangle=\delta_{mn}(1-e^{-\beta})e^{-\beta n}.$$
--
--   Both $\rho_\beta$ and $\rho_{\beta_{\rm out}}$ are densities of finite mean energy, $\beta_{\rm out}>0$, and the exact Gaussian displacement channel satisfies
--
--   $$\Phi_v(\rho_\beta)=\rho_{\beta_{\rm out}},\qquad E(\rho_{\beta_{\rm out}})=E(\rho_\beta)+v.$$
--
--   The same geometric matrix formula with $\beta$ replaced by $\beta_{\rm out}$ specifies the output. This is Gibbs propagation, with no classification or minimization assertion.
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, PDF p. 4, Section V, Eqs.(12)–(13): propagation of Gibbs input

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory

open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF p.4, Eqs.(12)–(13): exact Gibbs propagation with normalized full
geometric spectra. The output beta is positive and its mean is the input mean plus v. -/
theorem thermalOutput (beta v : ℝ) (hbeta : 0 < beta) (hv : 0 ≤ v) :
    B.IsDensity (A.photonMeanThermalState (gibbsMean beta)) ∧
    B.IsDensity (A.photonMeanThermalState (gibbsMean (outputBeta beta v))) ∧
    0 < outputBeta beta v ∧
    A.displacementNoiseChannel v (A.photonMeanThermalState (gibbsMean beta)) = (A.photonMeanThermalState (gibbsMean (outputBeta beta v))) ∧
    (∀ m n, (A.photonMeanThermalState (gibbsMean beta)) (B.fockKet n) m =
      if m = n then ((1 - Real.exp (-beta)) * Real.exp (-beta * n) : ℝ) else 0) ∧
    (∀ m n, (A.photonMeanThermalState (gibbsMean (outputBeta beta v))) (B.fockKet n) m =
      if m = n then ((1 - Real.exp (-outputBeta beta v)) *
        Real.exp (-outputBeta beta v * n) : ℝ) else 0) ∧
    A.FiniteEnergy (A.photonMeanThermalState (gibbsMean beta)) ∧
    A.FiniteEnergy (A.photonMeanThermalState (gibbsMean (outputBeta beta v))) ∧
    B.photonMean (A.photonMeanThermalState (gibbsMean (outputBeta beta v))) =
      B.photonMean (A.photonMeanThermalState (gibbsMean beta)) + v := by sorry

end QAlgorithms.Papers.Independent.Next46.P27

end
