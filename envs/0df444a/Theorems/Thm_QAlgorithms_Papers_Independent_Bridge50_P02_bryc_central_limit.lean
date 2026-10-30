-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P02_bryc_central_limit
-- name    : QAlgorithms.Papers.Independent.Bridge50.P02.bryc_central_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:41:52.470078+00:00
-- url     : https://prove2.me/theorems/efe2a09c-098f-44ad-8ed0-b28dad613c3a
-- title:
--   Theorem 2 (Bryc): analytic cumulants imply a central limit theorem
-- statement:
--   Let $X_n$ be measurable real random variables on probability spaces that may vary with $n$. Let $w_n>0$ tend to infinity; monotonicity is not required. Suppose that for a common $r>0$ the real exponential moments $\mathbb E e^{-xX_n}$ are finite for $|x|<r$ and their real logarithms extend to holomorphic functions $H_n$ on $|z|<r$. Assume that $H_n(x)/w_n$ converges for each real $|x|<r$ and that $|H_n(z)|/w_n$ is uniformly bounded. There is an analytic extension $H$ of the limit, and
--   $$\frac{X_n+H_n'(0)}{\sqrt{w_n}}\ \xrightarrow{\mathrm d}\ \mathcal N(0,H''(0)).$$
--   The variance $H''(0)$ is real and nonnegative; variance zero denotes the point mass at zero. Convergence in distribution is expressed by convergence of integrals of every bounded continuous real function. The centering has a plus sign because $H_n'(0)=-\mathbb E X_n$.
--
--   This form of Bryc's theorem supplies a central limit theorem without independence or identical distribution.
-- source:
--   Second-order asymptotics for quantum hypothesis testing in settings beyond i.i.d. - quantum lattice systems and more, arXiv:1510.04682v4, PDF p. 11, Theorem 2 (Bryc)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P02

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P02

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15
  (evaluate positiveMatrixRpow modularMatrix modularQuadratic resolventOverlap petzOverlap
    finiteRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower testingBeta)

open QAlgorithms.Papers.Independent.Information100.P58 (normalQuantile)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Theorem 2 (Bryc), PDF p.11 and Appendix A p.30. No independence or monotonicity
of weights. The PLUS centering is H_n'(0)=-E[X_n]. -/
theorem bryc_central_limit (X : ℕ → RandomVariable) (w : ℕ → ℝ)
    (hw : ∀ k, 0 < w k) (hdiverge : Tendsto w atTop atTop)
    (r : ℝ) (hr : 0 < r) (H : ℕ → ℂ → ℂ)
    (hexponential : ∀ k x, |x| < r →
      Integrable (fun a => Real.exp (-x * (X k).value a)) (X k).measure)
    (hanalytic : ∀ k, AnalyticOnNhd ℂ (H k) (Metric.ball 0 r))
    (hreal : ∀ k x, |x| < r → H k (x : ℂ) = (logLaplace (X k) x : ℂ))
    (hlimit : ∀ x : ℝ, |x| < r → ∃ l : ℂ,
      Tendsto (fun k => H k (x : ℂ) / (w k : ℂ)) atTop (nhds l))
    (hbounded : ∃ C : ℝ, ∀ k z, ‖z‖ < r → ‖H k z‖ ≤ C * w k) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.ball 0 r) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r,
        Tendsto (fun k => H k z / (w k : ℂ)) atTop (nhds (G z))) ∧
      (deriv (deriv G) 0).im = 0 ∧ 0 ≤ (deriv (deriv G) 0).re ∧
      BrycWeakLimit X w (deriv (deriv G) 0).re := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P02

end
