-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_proposition_14
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.proposition_14
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:30:55.499997+00:00
-- url     : https://prove2.me/theorems/2ce1f297-3940-4eee-aaf8-5c4f030132cd
-- title:
--   Proposition 14: proposition 14
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $W:X\to\mathcal S$ be a channel from an arbitrary nonempty set, with no countability or topology assumption on $X$, and fix $0<\varepsilon<1$. Let $M^*(W^n,\varepsilon)$ optimize finite nonempty uniform-message codes with average decoding error at most $\varepsilon$ and an arbitrary collective POVM. Put $S=\overline{\operatorname{im}W}$, $v_\varepsilon(S)=v_{\min}(S)$ for $\varepsilon\le1/2$ and $v_{\max}(S)$ otherwise, and let $\Phi^{-1}$ be the standard normal quantile. Fix $0<\eta<\varepsilon$ and a finite output alphabet $X_0\subseteq\operatorname{im}W$. For a probability mass function $P$ on $X_0$, put $\bar\rho_P=\sum_\rho P(\rho)\rho$, $\omega_P=\bigoplus_\rho P(\rho)\rho$, and $\zeta_P=\bigoplus_\rho P(\rho)\bar\rho_P$. Then
--   $$
--   \log_2 M^*(W,\varepsilon)\ge\sup_{P\in\mathcal P(X_0)}D_h^{\varepsilon-\eta}(\omega_P\|\zeta_P)-
--   \log_2\frac{4\varepsilon(1-\varepsilon+\eta)}{\eta^2}.
--   $$
--   This is the paper's local Wang–Renner achievability bound. It uses the actual image, rather than silently invoking the subsequent closure extension (54).
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 15, Proposition 14

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

/-- Proposition 14, PDF p.15, (53), attributed to Wang–Renner [43, Theorem 1].
The discrete specialization is finite as used in the source. It uses the ACTUAL
image; the separate closure extension (54) is not silently substituted. -/
theorem proposition_14 {X : Type*} {I : Type} [Nonempty X] [Fintype I] [DecidableEq I] [Nonempty I]
    (W : X → Mat I) (hW : ∀ x, QAlgorithms.IsDensityMatrix (W x))
    (e eta : ℝ) (he : 0 < e ∧ e < 1) (heta : 0 < eta ∧ eta < e)
    (X0 : Set (Mat I)) (hfinite : X0.Finite) (hX0 : X0 ⊆ Set.range W) :
    (⨆ E : {E : Ensemble I // ∀ i, E.state i ∈ X0},
      normalizedTestingDivergence (e-eta) (cqJointState E.val) (referenceState E.val)) ≤
    ENNReal.ofReal (logTwo (cqOptimalMessages W e) + logTwo (4*e*(1-e+eta)/eta^2)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
