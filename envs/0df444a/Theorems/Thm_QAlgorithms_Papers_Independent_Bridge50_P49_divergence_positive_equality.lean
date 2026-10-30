-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P49_divergence_positive_equality
-- name    : QAlgorithms.Papers.Independent.Bridge50.P49.divergence_positive_equality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:21:43.541985+00:00
-- url     : https://prove2.me/theorems/836aa778-e4bd-4d9c-ab10-27e2fe94b9bd
-- title:
--   Positivity and equality for sandwiched Rényi divergence
-- statement:
--   Let $\rho$ and $\sigma$ be density matrices on the same finite-dimensional Hilbert space, and let $\alpha>0$, $\alpha\ne1$. In this paper, $D_\alpha(\rho\|\sigma)=\frac1{\alpha-1}\log\operatorname{Tr}\!\left[(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha\right]$ when $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$, and $+\infty$ otherwise, also when $\alpha<1$. Powers use the inverse on the spectral support and logarithms are natural. Then
--
--   $$D_\alpha(\rho\|\sigma)\geq0,\qquad D_\alpha(\rho\|\sigma)=0\ \Longleftrightarrow\ \rho=\sigma.$$
--
--   The assertion includes singular states and the full positive-order range other than one.
-- source:
--   Sandwiched Rényi Divergence Satisfies Data Processing Inequality, arXiv:1306.5920v6, PDF p. 8, Theorem 5 (Positivity and equality condition)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P49

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P49

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower Dominates rawTrace leftMarginal rightMarginal marginalAB marginalAC)

/-- Beigi, arXiv:1306.5920v6, Theorem 5, PDF p.8: full positive-order domain,
including singular states and support failure. Both clauses are retained. -/
theorem divergence_positive_equality {I : Type} [Fintype I] [DecidableEq I]
    (a : ℝ) (ha : 0 < a) (haone : a ≠ 1) (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    0 ≤ beigiSandwichedDivergence a rho sigma ∧ (beigiSandwichedDivergence a rho sigma = 0 ↔ rho = sigma) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P49

end
