-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_18
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_18
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:33:49.027813+00:00
-- url     : https://prove2.me/theorems/110d974d-a6b4-4225-828e-89f0b665a551
-- title:
--   Lemma 18: lemma 18
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. For each $0<\gamma<1$, there is a finite set $G^\gamma\subseteq\mathcal S$ such that
--   $$
--   |G^\gamma|\le(5/\gamma)^{2d^2}(2d/\gamma+2)^{d-1}.
--   $$
--   For every $\rho\in\mathcal S$ there is one $\tau\in G^\gamma$ satisfying all three conditions
--   $$
--   \tfrac12\|\rho-\tau\|_1\le\gamma,\qquad D(\rho\|\tau)\le4\gamma(2d+1),\qquad
--   \lambda_{\min}(\tau)\ge\frac\gamma{2d+\gamma}.
--   $$
--   This asserts existence of a simultaneous approximation net, without identifying it with the flawed construction printed in Appendix C.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 18, Lemma 18

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50

noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P50

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; these names do not create local declarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)

open QAlgorithms.Papers.Independent.Information100.P69 (entropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)

open QAlgorithms (vnEntropy traceDistance minEigenvalue)

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelSpace

/-- Lemma 18, PDF pp.18,29–30: existence of a finite net with all three simultaneous
approximation properties. This does not assert that the defective Appendix-C formula works. -/
theorem lemma_18 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (g : ℝ) (hg : 0 < g ∧ g < 1) :
    ∃ G : Finset (Mat I), NetConditions g G := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
