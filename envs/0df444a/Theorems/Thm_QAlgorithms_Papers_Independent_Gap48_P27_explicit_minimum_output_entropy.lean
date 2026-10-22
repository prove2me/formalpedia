-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_explicit_minimum_output_entropy
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.explicit_minimum_output_entropy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:24:13.744473+00:00
-- url     : https://prove2.me/theorems/82cae9dc-4233-4e81-bd5f-982e3b5dc9dd
-- title:
--   §4 Eq. (30): explicit multimode minimum output entropy
-- statement:
--   Let $\Phi$ be a Gaussian gauge-covariant or gauge-contravariant channel with gain $K$ and noise $\mu$, and let $n\ge1$ be an integer. Set $A=\mu+(KK^*-I)/2$, which is positive semidefinite by the relevant CP condition. With $g(x)=(x+1)\ln(x+1)-x\ln x$ and $g(0)=0$,
--
--   $$
--   \min_{\rho^{(n)}\in\mathcal S_2}S(\Phi^{\otimes n}[\rho^{(n)}])
--   =n\,\operatorname{tr}g(A).
--   $$
--
--   The product vacuum attains the minimum over arbitrary correlated block inputs. Here $g(A)$ is Hermitian functional calculus and the trace is on the finite output phase space. This provides the explicit value of the unconditional vacuum minimum.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 13, §4 Eq. (30): explicit multimode minimum output entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P27

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P27

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass IsTraceClassChannel rankOne
   productCoeff tensorApply traceSize BreaksTraceClassEntanglement)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats GeneralizedEnsemble HasAverage
   finiteEnsembleCapacity ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel vacuum productCoherentKernel modeEnergy husimi FockPOVM
   realFockTracePair)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (traceClassTensorMap traceClassChannelPower)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation partialRight partialLeft isometryCoeff conjugateKernel)

/-- §4, PDF p.13, (30), extended to contravariant channels in the final
sentence of §4. CP makes the occupation matrix nonnegative, including its
zero eigenvalues. The product vacuum attains the stated minimum.
The displayed trace applies accepted g to the occupation matrix via functional
calculus; frozen Claimed50.P36.matrixEntropy is instead -tr(rho log rho) on a
density matrix and cannot be applied to this occupation matrix. -/
theorem explicit_minimum_output_entropy {a b : ℕ} (G : GaugeChannel a b)
    (n : ℕ) (hn : 0 < n) :
    (vacuumOccupation G).PosSemidef ∧
    minimizesOn (traceClassChannelPower G.operation n) blockFiniteMoments (blockVacuum a n) ∧
    extendedEntropyNats (traceClassChannelPower G.operation n (blockVacuum a n)) =
      ENNReal.ofReal ((n : ℝ) *
        (Matrix.trace (cfc (fun z : ℂ => (g z.re : ℂ)) (vacuumOccupation G))).re) ∧
    domainMinimumEntropy (traceClassChannelPower G.operation n) blockFiniteMoments =
      ENNReal.ofReal ((n : ℝ) *
        (Matrix.trace (cfc (fun z : ℂ => (g z.re : ℂ)) (vacuumOccupation G))).re) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
