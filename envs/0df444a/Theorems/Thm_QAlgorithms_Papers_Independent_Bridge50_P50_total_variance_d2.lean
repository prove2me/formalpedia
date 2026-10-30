-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_total_variance_d2
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.total_variance_d2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:43:19.880327+00:00
-- url     : https://prove2.me/theorems/7c2f94ac-71a7-4004-88e9-e7e8febedd4c
-- title:
--   Total Variance D2: total variance d2
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $P$ be any finite ensemble of states, allowing zero probabilities, with $\bar\rho_P=\sum_\rho P(\rho)\rho$. Set $\omega_P=\bigoplus_\rho P(\rho)\rho$, $\zeta_P=\bigoplus_\rho P(\rho)\bar\rho_P$, and $I(P)=\sum_\rho P(\rho)D(\rho\|\bar\rho_P)$. Then
--   $$
--   V(\omega_P\|\zeta_P)=\sum_\rho P(\rho)V(\rho\|\bar\rho_P)+
--   \sum_\rho P(\rho)\bigl(D(\rho\|\bar\rho_P)-I(P)\bigr)^2.
--   $$
--   This is the complete law of total variance for block states. The second term disappears for peripheral center decompositions, yielding Lemma 15.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 30, Total Variance D2

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

/-- Appendix D1, PDF p.30, (D1)–(D2): FULL law of total variance for any finite ensemble.
No equal-relative-entropy invariant is assumed. Zero-weight blocks contribute zero. -/
theorem total_variance_d2 {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (E : Ensemble I) :
    pairInformationVariance (cqJointState E) (referenceState E) = ensembleVariance E +
      ∑ i, E.prob i * ((entropy (E.state i) (ensembleAverage E)).toReal -
        finiteHolevoInformation E)^2 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
