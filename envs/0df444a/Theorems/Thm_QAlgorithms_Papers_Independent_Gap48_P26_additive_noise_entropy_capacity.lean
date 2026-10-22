-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P26_additive_noise_entropy_capacity
-- name    : QAlgorithms.Papers.Independent.Gap48.P26.additive_noise_entropy_capacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:58:58.49846+00:00
-- url     : https://prove2.me/theorems/703da452-a8f7-43c2-a440-64cbe28b2d50
-- title:
--   Additive Gaussian noise minimum entropy and capacity
-- statement:
--   For the additive Gaussian noise channel $\mathcal N_n$, let $n\ge0$ and $E\ge0$ be finite. Its characteristic action is $\chi(z)\mapsto\chi(z)e^{-n|z|^2}$. Let $g(x)=((x+1)\ln(x+1)-x\ln x)/\ln2$, with $g(0)=0$. Then
--
--   $$s_1(\mathcal N_n)=g(n),\qquad C(\mathcal N_n;E)=g(E+n)-g(n).$$
--
--   The minimum ranges over all normalized finite-energy pure Fock inputs, and the capacity is the unrestricted regularized value under the average photon budget. Zero noise gives the identity channel.
-- source:
--   Ultimate communication capacity of quantum optical channels by solving the Gaussian minimum-entropy conjecture, arXiv:1312.6225v1, PDF p. 7, Eqs. (26)-(27)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P26

open MeasureTheory Filter

open scoped ENNReal Topology BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Next46.P32 (NumberString vacuum)

open QAlgorithms.Papers.Independent.Next46.P45 (entanglementOfFormation)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State rankOne IsDensity IsBarycenter IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation traceClassTensorPower weylCharacteristic boundedUnitaryConjugation
   conjugateKernel partialRight GaussianDensity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.6-7, (26)-(27): additive classical Gaussian noise, with n=0 allowed. -/
theorem additive_noise_entropy_capacity
    (Phi : Operation ℕ ℕ) (n E : ℝ) (hn : 0 ≤ n) (hE : 0 ≤ E)
    (hPhi : PhaseInsensitive Phi 1 (2 * n)) :
    minimumFiniteEnergy id Phi = ENNReal.ofReal (thermalEntropyBits n) ∧
    regularizedClassicalBits Phi E = ENNReal.ofReal (thermalEntropyBits (E + n) - thermalEntropyBits n) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P26

end
