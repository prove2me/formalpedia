-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_proposition_19
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.proposition_19
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:34:19.963366+00:00
-- url     : https://prove2.me/theorems/7f8522f6-d217-4215-9e0c-a19d67811834
-- title:
--   Proposition 19: proposition 19
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $S\subseteq\mathcal S$ be nonempty and closed. Write $\chi(S)$ for its divergence radius, $\sigma_*(S)$ for its selected divergence center, $\Gamma(S)$ for its peripheral states, and $\Pi(S)$ for the probability measures supported on $\Gamma(S)$ with barycenter $\sigma_*(S)$. Probability measures are Borel measures, with the weak topology. Fix $\nu>0$. Define $\Delta(\rho,\Gamma)=\min_{\tau\in\Gamma(S)}\tfrac12\|\rho-\tau\|_1$ and, for a positive-length sequence of factors from $S$, let $\Omega_1^\nu$ mean $n^{-1}\sum_i\Delta(\rho_i,\Gamma)\le\nu$ and $\Omega_2^\nu$ mean $\tfrac12\|n^{-1}\sum_i\rho_i-\sigma_*\|_1\le\nu$.
--
--   There are $0<\gamma_0<1$ and a net $G^{\gamma_0}$ as in Lemma 18, depending on $S,\nu$ before the error parameter and sequence. Set
--   $$
--   \sigma_n=\tfrac12\sigma_*^{\otimes n}+\frac1{2|G^{\gamma_0}|}\sum_{\tau\in G^{\gamma_0}}\tau^{\otimes n}.
--   $$
--   For every $0<\varepsilon<1$ and error sequence with $|\varepsilon_n-\varepsilon|\le n^{-1/2}$, a fixed $N\ge1$ satisfies
--   $$
--   D_h^{\varepsilon_n}(\rho^n\|\sigma_n)\le n\chi(S)+\sqrt{n v_\varepsilon(S)}\Phi^{-1}(\varepsilon)
--   $$
--   for all $n\ge N$ and all factor sequences outside $\Omega_1^\nu\cap\Omega_2^\nu$. This controls the complement of the intersection, including the empty bad set when $\nu>1$.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 19, Proposition 19

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

/-- Proposition 19, PDF pp.19–20, (81): gamma and its net precede epsilon and the error
sequence; the comparison state is (78). Complement is of the INTERSECTION of good sets.
The same formulas for nu>1 give an empty bad set. -/
theorem proposition_19 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ClosedStateSet S) (nu : ℝ) (hnu : 0 < nu) :
    ∃ g : ℝ, 0 < g ∧ g < 1 ∧ ∃ G : Finset (Mat I), NetConditions g G ∧
    ∀ e : ℝ, 0 < e → e < 1 → ∀ es : ℕ → ℝ, ErrorEnvelope e es →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ rho : Fin n → Mat I,
        (∀ i, rho i ∈ S) → ¬ (OmegaOne S nu rho ∧ OmegaTwo S nu rho) →
        normalizedTestingDivergence (es n) (tensorWord rho) (auxiliaryState S G n) ≤
          ENNReal.ofReal (secondOrder S e n) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
