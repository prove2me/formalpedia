-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P44_singleModeCapacity
-- name    : QAlgorithms.Papers.Independent.Renew46.P44.singleModeCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:37:45.054033+00:00
-- url     : https://prove2.me/theorems/d7fecfea-0ba0-4579-ac01-6130fd42b998
-- title:
--   §V.1, (82)–(91): displaced thermal channel capacity and attainment
-- statement:
--   For $N,E\ge0$, consider the full oscillator alphabet $S_z=D(z)\tau_ND(z)^\dagger$ with modulation cost $|z|^2$. Codes use genuine product outputs and collective bounded sub-POVMs; each transmitted word has total modulation cost at most $nE$. Then
--
--   $$C=g(N+E)-g(N).$$
--
--   For $E>0$ the attaining Borel modulation law has density $(\pi E)^{-1}e^{-|z|^2/E}$; for $E=0$ it is Dirac at zero. This is a probability law of mean cost $E$, its output barycenter is $\tau_{N+E}$, and its Holevo information equals $C$. The output operators are actual normalized trace-class densities. This includes pure coherent signals at $N=0$ without evaluating a singular noise density.
-- source:
--   Coding Theorems for Quantum Channels, arXiv:quant-ph/9809023v1, PDF p. 25, §V.1, (82)–(91): displaced thermal channel capacity and attainment

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P44

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P44

open Filter MeasureTheory

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tracePair)

open QAlgorithms.Papers.Independent.Frontier30.P14 (traceClassTensorPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.23-25, (82)-(91): operational capacity and attaining modulation.
Both N=0 and E=0 are included, on the full infinite oscillator. -/
theorem singleModeCapacity (N E : ℝ) (hN : 0 ≤ N) (hE : 0 ≤ E) :
    (∀ z, TC.IsDensity (gaussianOutput N z)) ∧
    IsProbabilityMeasure (gaussianLaw E) ∧
    Integrable Complex.normSq (gaussianLaw E) ∧
    (∫ z, Complex.normSq z ∂gaussianLaw E) = E ∧
    integralAverage (gaussianOutput N) (gaussianLaw E) =
      F.thermalMatrix (2 * (N + E) + 1) ∧
    averageErrorCqCapacity (gaussianOutput N) Complex.normSq E = ENNReal.ofReal (g (N + E) - g N) ∧
    integralChi (gaussianOutput N) (gaussianLaw E) =
      averageErrorCqCapacity (gaussianOutput N) Complex.normSq E := by sorry

end QAlgorithms.Papers.Independent.Renew46.P44

end
