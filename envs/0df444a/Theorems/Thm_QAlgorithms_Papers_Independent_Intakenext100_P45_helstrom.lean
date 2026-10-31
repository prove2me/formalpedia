-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_helstrom
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.helstrom
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:58:11.406547+00:00
-- url     : https://prove2.me/theorems/d962a571-86ed-44d3-9881-d6b1be190d9a
-- title:
--   Unnumbered Holevo–Helstrom optimum (10)
-- statement:
--   For density operators $\rho,\sigma$ with priors $\pi_0,\pi_1>0$ summing to one, let $D=\pi_1\sigma-\pi_0\rho$. The projector onto $\operatorname{ran}D_+$ attains the minimum over every binary effect, and
--
--   $$P_e^*=\pi_1-\operatorname{Tr}D_+=\frac{1-\|D\|_1}{2}.$$
--
--   The outer factor $1/2$ applies to the complete expression. This is the finite-copy optimum used in the Chernoff theorem.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 8, Unnumbered Holevo–Helstrom optimum (10)

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

/-- arXiv:0708.4282v1, PDF pp.8,9: Unnumbered Holevo–Helstrom optimum (10). -/
theorem helstrom (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (p0 p1 : ℝ) (h0 : 0 < p0) (h1 : 0 < p1) (hp : p0+p1=1) :
    let D := (p1 : ℂ) • sigma - (p0 : ℂ) • rho
    let Pstar := positiveProjection D
    IsProjection Pstar ∧ IsEffect Pstar ∧
    bayesError rho sigma Pstar p0 p1 = p1-(positivePart D).trace.re ∧
    p1-(positivePart D).trace.re = helstromError rho sigma p0 p1 ∧
    (∀ P : Mat I, IsEffect P →
      helstromError rho sigma p0 p1 ≤ bayesError rho sigma P p0 p1) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
