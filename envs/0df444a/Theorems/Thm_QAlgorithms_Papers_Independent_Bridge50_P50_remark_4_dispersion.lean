-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_remark_4_dispersion
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.remark_4_dispersion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:41:11.553195+00:00
-- url     : https://prove2.me/theorems/903d0991-2220-46c3-bddf-652187c08da4
-- title:
--   Remark 4 Dispersion: remark 4 dispersion
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $W:X\to\mathcal S$ be a channel from an arbitrary nonempty set, with no countability or topology assumption on $X$, and fix $0<\varepsilon<1$. Let $M^*(W^n,\varepsilon)$ optimize finite nonempty uniform-message codes with average decoding error at most $\varepsilon$ and an arbitrary collective POVM. Put $S=\overline{\operatorname{im}W}$, $v_\varepsilon(S)=v_{\min}(S)$ for $\varepsilon\le1/2$ and $v_{\max}(S)$ otherwise, and let $\Phi^{-1}$ be the standard normal quantile. Assume also $\varepsilon\ne1/2$, so the displayed denominator is nonzero. Then
--   $$
--   \limsup_{n\to\infty}\frac1n\left(\frac{nC(W)-\log_2 M^*(W^n,\varepsilon)}{\Phi^{-1}(\varepsilon)}\right)^2=v_\varepsilon(S).
--   $$
--   This gives the operational interpretation of the geometric dispersion. The exclusion of $1/2$ repairs the omitted domain restriction of (26) only; Theorem 4 still includes $1/2$.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 8, Remark 4 Dispersion

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

/-- Remark 4, PDF p.8, (26): operational dispersion equals the selected peripheral
variance. The source omits the necessary exclusion e=1/2 (zero denominator); this
restriction is local to this remark and is recorded as a source boundary discrepancy. -/
theorem remark_4_dispersion {X I : Type*} [Nonempty X] [Fintype I] [DecidableEq I] [Nonempty I]
    (W : X → Mat I) (hW : ∀ x, QAlgorithms.IsDensityMatrix (W x))
    (e : ℝ) (he : 0 < e ∧ e < 1) (hne : e ≠ 1/2) :
    Filter.limsup (fun n : ℕ => (1/(n : ℝ)) *
      ((n * cqOperationalCapacity W - blockLog W e n) / normalQuantile e)^2) atTop =
      vEpsilon (closure (Set.range W)) e := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
