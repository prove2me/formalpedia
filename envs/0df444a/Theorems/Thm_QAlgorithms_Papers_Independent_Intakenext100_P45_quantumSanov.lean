-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_quantumSanov
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.quantumSanov
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:22:13.173+00:00
-- url     : https://prove2.me/theorems/54018c27-d989-4e1d-a9a9-36b717fc8ee3
-- title:
--   §5.6, quantum Sanov theorem
-- statement:
--   Let $\Gamma$ be any family of densities on a fixed finite-dimensional space, and let $\sigma$ be a density. There exists one sequence of orthogonal projections such that $\alpha_n(\rho)\to0$ for every $\rho\in\Gamma$, and
--
--   $$\beta_R=\inf_{\rho\in\Gamma}S(\rho\|\sigma).$$
--
--   Every sequence of binary effects with the same pointwise vanishing type-I errors has upper type-II rate at most this infimum. No uniform convergence or compactness assumption is imposed. For $\Gamma=\varnothing$, the extended infimum is $+\infty$ and the null constraint is vacuous.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 31, §5.6, quantum Sanov theorem

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

/-- arXiv:0708.4282v1, PDF p.31: §5.6, quantum Sanov theorem. -/
theorem quantumSanov (Gamma : Set (Mat I)) (hGamma : ∀ rho ∈ Gamma, IsDensityMatrix rho)
    (sigma : Mat I) (hsigma : IsDensityMatrix sigma) :
    let D : EReal := sInf {v | ∃ rho ∈ Gamma, v=relativeEntropy rho sigma}
    (∃ P : QuantumTests I, (∀ k, IsProjection (P k)) ∧
      (∀ rho ∈ Gamma, Tendsto (quantumAlpha rho P) atTop (nhds 0)) ∧
      HasRate (quantumBeta sigma P) D) ∧
    (∀ P : QuantumTests I, (∀ k, IsEffect (P k)) →
      (∀ rho ∈ Gamma, Tendsto (quantumAlpha rho P) atTop (nhds 0)) →
      Filter.limsup (fun k => rateTerm (quantumBeta sigma P k) k) atTop ≤ D) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
