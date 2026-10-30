-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_29
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_29
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:39:40.104993+00:00
-- url     : https://prove2.me/theorems/8b8f8de4-f6f3-418c-b5d1-fb1681b250f8
-- title:
--   Lemma 29: lemma 29
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $S\subseteq\mathcal S$ be finite. For a probability mass function $P$ on $S$, set $\bar\rho_P=\sum_\rho P(\rho)\rho$, $V(P)=\sum_\rho P(\rho)V(\rho\|\bar\rho_P)$ and $T(P)=\sum_\rho P(\rho)T(\rho\|\bar\rho_P)$, with zero-weight terms equal to zero and $T$ the centered NS absolute third moment. There are constants $V^*,T^*\in\mathbb R$, chosen before $P$, such that
--   $$
--   \forall P\in\mathcal P(S):\quad V(P)\le V^*,\qquad T(P)\le T^*.
--   $$
--   The barycenter is constructed from $P$ and need not have full rank. This is the finite discrete/simplex reading used by the proof.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 28, Lemma 29

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

/-- Lemma 29, PDF p.28: two constants chosen before every probability mass function
on the fixed finite alphabet. No full-rank barycenter is required. -/
theorem lemma_29 {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ∀ rho ∈ S, QAlgorithms.IsDensityMatrix rho) (hfinite : S.Finite) :
    ∃ V T : ℝ, ∀ E : Ensemble I, (∀ i, E.state i ∈ S) →
      ensembleVariance E ≤ V ∧ ensembleThird E ≤ T := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
