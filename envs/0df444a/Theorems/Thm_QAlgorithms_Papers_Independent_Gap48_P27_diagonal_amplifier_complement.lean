-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_diagonal_amplifier_complement
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.diagonal_amplifier_complement
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:18:04.096879+00:00
-- url     : https://prove2.me/theorems/382e7607-4e07-4a2b-b65d-0ba711d83c9a
-- title:
--   Proposition 3: complementary quantum-limited diagonal channels
-- statement:
--   Fix a finite common mode count $s$ and nonnegative amplitude gains $k_j\ge1$. Let $\Phi$ be the quantum-limited amplifier with gain $\operatorname{diag}(k_j)$, and let $\widetilde\Phi$ be the quantum-limited contravariant channel whose antilinear gain is $\operatorname{diag}(\sqrt{k_j^2-1})\Lambda$, where $\Lambda$ is complex conjugation. There is a common Stinespring isometry $V$ into the signal/environment product such that, for every trace-class $X$,
--
--   $$
--   \Phi[X]=\operatorname{Tr}_E(VXV^*),\qquad
--   \widetilde\Phi[X]=\operatorname{Tr}_B(VXV^*).
--   $$
--
--   Thus they are mutually complementary, including gain-one signal modes and their vacuum environmental outputs. The proposition transfers output-entropy properties between these two channel classes.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 10, Proposition 3: complementary quantum-limited diagonal channels

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

/-- Proposition 3, PDF p.10, citing [23] and [11] §12.6.1: common-mode
nonnegative diagonal amplifier and contravariant complement. Lambda is outside
the radical; gains equal to one give vacuum complementary modes. -/
theorem diagonal_amplifier_complement {s : ℕ} (gain : Fin s → ℝ)
    (hgain : ∀ j, 1 ≤ gain j) (A B : GaugeChannel s s)
    (hA : quantumLimitedAmplifier A) (hB : quantumLimitedContravariant B)
    (hKA : A.gain = Matrix.diagonal (fun j => (gain j : ℂ)))
    (hKB : B.gain = Matrix.diagonal (fun j => (Real.sqrt (gain j ^ 2 - 1) : ℂ))) :
    ∃ V : Hilbert (NumberString s) →ₗᵢ[ℂ]
        Hilbert (NumberString s × NumberString s),
      ∀ X, IsTraceClass X →
        A.operation X = partialRight (conjugateKernel (isometryCoeff V) X) ∧
        B.operation X = partialLeft (conjugateKernel (isometryCoeff V) X) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
