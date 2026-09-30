-- Prove2me | Theorems.Thm_SupplyChainTheory_bullwhip_lemma_13_1
-- name    : SupplyChainTheory.bullwhip_lemma_13_1
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T00:02:03.516924+00:00
-- url     : https://prove2.me/theorems/aaf80554-fb9d-49c2-a34c-55871597c70c
-- title:
--   Lemma 13.1: $\mathrm{Cov}[D_{t-i}, \hat\sigma^L_{et}] = 0$ for $i = 1, \dots, m$
-- statement:
--   **Lemma 13.1.** For the stationary Gaussian AR(1) demand and the forecast-error estimate
--   $\hat\sigma^L_{et} = C\sqrt{\sum_{i=1}^m e_{t-i}^2/m}$ of Eq. (13.8), with $m \ge 1$,
--
--   $$ \mathrm{Cov}\big[D_{t-i},\ \hat\sigma^L_{et}\big] \;=\; 0 \qquad\text{for all } i = 1, \dots, m. $$
--
--   The book omits the proof and cites Ryan (1997). The reason is symmetry: the forecast errors
--   $e_{t-1}, \dots, e_{t-m}$ are linear functions of the demands, hence jointly Gaussian with
--   mean zero, $\hat\sigma^L_{et}$ is an even function of them, and the regression of any demand on
--   the error vector is an odd function of it, so the covariance is the expectation of an odd
--   function of a centred Gaussian vector. The lemma is what removes the cross terms between the
--   demand part and the safety-stock part of $Q_t$ in the variance computation of Theorem 13.2.
--
--   **Formalization Note** The estimate is stated with the book's unspecified constant $C_{L\rho}$
--   as a free parameter $C$; the covariance does not depend on it.
-- source:
--   Lawrence V. Snyder and Zuo-Jun Max Shen, Fundamentals of Supply Chain Theory, 2nd ed., Wiley 2019, DOI 10.1002/9781119584445, p. 545, Sect. 13.2.2, Lemma 13.1: 'Cov[Dt-i, sigma-hat] = 0 for all i = 1, ..., m. Proof. Omitted; see Ryan (1997)'

import Definitions.Def_SupplyChainTheory_bullwhip

namespace SupplyChainTheory

theorem bullwhip_lemma_13_1 {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] (X : AR1Demand P) (C : ℝ) (m : ℕ) (hm : 0 < m)
    (t : ℤ) (i : ℕ) (hi1 : 1 ≤ i) (him : i ≤ m) :
    ProbabilityTheory.covariance (X.D (t - i)) (X.sigmaHat C m t) P = 0 := by sorry

end SupplyChainTheory
