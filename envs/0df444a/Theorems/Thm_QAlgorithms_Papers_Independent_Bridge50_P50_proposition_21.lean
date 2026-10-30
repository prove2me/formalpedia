-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_proposition_21
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.proposition_21
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:35:39.778718+00:00
-- url     : https://prove2.me/theorems/56a54caf-f568-4065-b3c0-5f8b2d755883
-- title:
--   Proposition 21: proposition 21
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $S\subseteq\mathcal S$ be nonempty and closed. Write $\chi(S)$ for its divergence radius, $\sigma_*(S)$ for its selected divergence center, $\Gamma(S)$ for its peripheral states, and $\Pi(S)$ for the probability measures supported on $\Gamma(S)$ with barycenter $\sigma_*(S)$. Probability measures are Borel measures, with the weak topology. Fix $0<\varepsilon<1$ and a real sequence $(\varepsilon_n)_{n\ge1}$ satisfying $|\varepsilon_n-\varepsilon|\le n^{-1/2}$. Write $\chi_h^a(A)=\inf_{\sigma\in\mathcal S}\sup_{\rho\in A}D_h^a(\rho\|\sigma)$ for the normalized testing radius, and $S^{\otimes n}$ for the set of product states with all factors in $S$. For every $\delta>0$, a fixed $N\ge1$ satisfies
--   $$
--   \chi_h^{\varepsilon_n}(S^{\otimes n})\le n\chi(S)+\sqrt{n v_\varepsilon(S)}\Phi^{-1}(\varepsilon)+\delta\sqrt n\qquad(n\ge N).
--   $$
--   This is precisely the one-sided $o(\sqrt n)$ upper remainder, including zero variance and $\varepsilon=1/2$. It asserts no absolute expansion for the testing radius.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 21, Proposition 21

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

/-- Proposition 21, PDF pp.21–22, (92): only an upper remainder, valid also at zero
variance and epsilon=1/2. Positive-part small-o is exactly a one-sided o(sqrt n) bound. -/
theorem proposition_21 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ClosedStateSet S) (e : ℝ) (he : 0 < e ∧ e < 1)
    (es : ℕ → ℝ) (hes : ErrorEnvelope e es) :
    ∀ delta : ℝ, 0 < delta → ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      testingRadius (productSet S n) (es n) ≤
        ENNReal.ofReal (secondOrder S e n + delta * Real.sqrt n) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
