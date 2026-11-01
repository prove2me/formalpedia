-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P05_gentle_measurement
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P05.gentle_measurement
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:01:02.959192+00:00
-- url     : https://prove2.me/theorems/74fda146-75b2-44b5-a47c-d60250fe6fde
-- title:
--   Gentle measurement with constant two
-- statement:
--   Let $\rho$ be a positive semidefinite trace-one operator on a finite-dimensional complex Hilbert space, and let $X$ be any effect, so $0\le X\le I$. Then
--
--   $$\left\|\rho-\sqrt X\,\rho\sqrt X\right\|_1\le2\sqrt{\operatorname{Tr}[\rho(I-X)]}.$$
--
--   Here $\|A\|_1=\operatorname{Tr}\sqrt{A^*A}$ is the full trace norm, and $\sqrt X\,\rho\sqrt X$ is the unnormalized postmeasurement operator. Singular effects and zero rejection probability are included. This bound controls the disturbance caused by a likely measurement outcome.
-- source:
--   A New Proof of the Channel Coding Theorem via Hypothesis Testing in Quantum Information Theory, arXiv:quant-ph/0208139v1, PDF p. 10, Lemma 5, (57)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P05

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P05

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter Topology QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positiveProjection)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr pinch typeI accept)

open QAlgorithms.Papers.Independent.Claimed50.P45 (pinchedTest)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)

open QAlgorithms.Papers.Independent.Dependency50.P35 (directSum)

open QAlgorithms.Papers.Independent.Renew46.P44 (wordOutput)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {X I : Type} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]

/-- PDF p.10, Lemma 5, (57): gentle measurement with constant 2 in the FULL
trace norm. The postmeasurement operator is unnormalized; zero effects,
singular effects, and zero rejection probability are allowed. -/
theorem gentle_measurement (rho E : Mat I) (hrho : IsDensityMatrix rho)
    (hE : IsEffect E) :
    traceNorm (rho - cfc Real.sqrt E * rho * cfc Real.sqrt E) ≤
      2 * Real.sqrt (tr (rho * (1 - E))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P05

end
