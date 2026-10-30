-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_proposition_5
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.proposition_5
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:26:25.049912+00:00
-- url     : https://prove2.me/theorems/3781716b-b10e-4ab0-91e0-e0a5cfdb6c49
-- title:
--   Proposition 5: proposition 5
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $W:X\to\mathcal S$ be a channel from an arbitrary nonempty set, with no countability or topology assumption on $X$, and fix $0<\varepsilon<1$. Let $M^*(W^n,\varepsilon)$ optimize finite nonempty uniform-message codes with average decoding error at most $\varepsilon$ and an arbitrary collective POVM. Put $S=\overline{\operatorname{im}W}$, $v_\varepsilon(S)=v_{\min}(S)$ for $\varepsilon\le1/2$ and $v_{\max}(S)$ otherwise, and let $\Phi^{-1}$ be the standard normal quantile. For every $0<\mu<1-\varepsilon$, using the actual image in the testing radius,
--   $$
--   \log_2 M^*(W,\varepsilon)\le\chi_h^{\varepsilon+\mu}(\operatorname{im}W)+
--   \log_2\frac{\varepsilon+\mu}{\mu(1-\varepsilon-\mu)}.
--   $$
--   The testing radius optimizes the comparison state before taking the supremum over channel outputs. This is a one-shot converse for arbitrary input alphabets.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 9, Proposition 5

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

/-- Proposition 5, PDF p.9, (28): actual image, normalized divergence and full penalty. -/
theorem proposition_5 {X I : Type*} [Nonempty X] [Fintype I] [DecidableEq I] [Nonempty I]
    (W : X → Mat I) (hW : ∀ x, QAlgorithms.IsDensityMatrix (W x))
    (e mu : ℝ) (he : 0 < e ∧ e < 1) (hmu : 0 < mu ∧ mu < 1-e) :
    ENNReal.ofReal (logTwo (cqOptimalMessages W e)) ≤ testingRadius (Set.range W) (e+mu) +
      ENNReal.ofReal (logTwo ((e+mu)/(mu*(1-e-mu)))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
