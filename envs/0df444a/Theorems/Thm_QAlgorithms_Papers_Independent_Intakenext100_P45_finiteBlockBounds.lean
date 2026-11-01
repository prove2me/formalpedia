-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_finiteBlockBounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.finiteBlockBounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:20:53.743987+00:00
-- url     : https://prove2.me/theorems/d08d2df9-3742-45a9-a4d9-c5f54a3c2ffe
-- title:
--   §5.5, finite-block bounds (49)–(52)
-- statement:
--   For density operators $\rho,\sigma$, $n\ge1$, $x\in\mathbb R$, and $0<s<1$, let $P_n$ project onto the range of $(e^{-nx}\sigma^{\otimes n}-\rho^{\otimes n})_+$. Then
--
--   $$\beta_n(P_n)\le e^{nx(1-s)}Q_s^n,\qquad\alpha_n(P_n)\le e^{-nxs}Q_s^n,$$
--
--   where $Q_s=\operatorname{Tr}(\rho^{1-s}\sigma^s)$. These product forms include $Q_s=0$. The test is tied to the displayed threshold; no finite-block optimization over unrelated parameters is asserted.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 29, §5.5, finite-block bounds (49)–(52)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P45

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P45

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder ENNReal BigOperators Topology

open QAlgorithms.Papers.Independent.Information100.P07
  (support positivePart positiveProjection IsProjection)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Dependency50.P28 (logNonnegativeExtended relativeEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P15 (positiveMatrixRpow)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:0708.4282v1, PDF pp.29,30: §5.5, finite-block bounds (49)–(52). Source correction: PDF p.30 optimizes a fixed-s test over other s without justification. Retain actual (51)--(52); Theorem 5 separately states full asymptotic existence. Independent moderation required. -/
theorem finiteBlockBounds (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (s x : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ) (hn : 0 < n) :
    let P := positiveProjection (((Real.exp (-(n : ℝ)*x) : ℝ) : ℂ) • copies n sigma-copies n rho)
    IsProjection P ∧ IsEffect P ∧
    typeIIError (copies n sigma) P ≤ Real.exp ((n : ℝ)*x*(1-s)) * (chernoffOverlap rho sigma s)^n ∧
    typeIError (copies n rho) P ≤ Real.exp (-(n : ℝ)*x*s) * (chernoffOverlap rho sigma s)^n := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
