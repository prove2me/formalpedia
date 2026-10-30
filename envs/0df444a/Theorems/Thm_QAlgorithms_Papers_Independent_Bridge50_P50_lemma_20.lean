-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_20
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_20
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:34:56.340377+00:00
-- url     : https://prove2.me/theorems/ff78810d-6536-4133-8f2c-a860754c94bc
-- title:
--   Lemma 20: lemma 20
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $S\subseteq\mathcal S$ be nonempty and closed. Write $\chi(S)$ for its divergence radius, $\sigma_*(S)$ for its selected divergence center, $\Gamma(S)$ for its peripheral states, and $\Pi(S)$ for the probability measures supported on $\Gamma(S)$ with barycenter $\sigma_*(S)$. Probability measures are Borel measures, with the weak topology. Fix $n\ge1$, factors $\rho_i\in S$ and $0<\nu<1$. Let $\Delta(\rho,\Gamma)=\min_{\tau\in\Gamma(S)}\tfrac12\|\rho-\tau\|_1$. If $n^{-1}\sum_i\Delta(\rho_i,\Gamma)>\nu$, there is $\Xi\subseteq\{1,\ldots,n\}$ such that
--   $$
--   |\Xi|>n\nu/2,\qquad \forall i\in\Xi:\ \Delta(\rho_i,\Gamma)>\nu/2.
--   $$
--   Both inequalities are strict. This extracts many components separated from the peripheral set.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 20, Lemma 20

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

/-- Lemma 20, PDF pp.20,30: both inequalities are strict and n is positive. -/
theorem lemma_20 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ClosedStateSet S) (n : ℕ) (hn : 1 ≤ n)
    (rho : Fin n → Mat I) (hrho : ∀ i, rho i ∈ S)
    (nu : ℝ) (hnu : 0 < nu ∧ nu < 1) (hbad : ¬ OmegaOne S nu rho) :
    ∃ Xi : Finset (Fin n), (n : ℝ) * nu / 2 < Xi.card ∧
      ∀ i ∈ Xi, nu/2 < peripheralDistance S (rho i) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
