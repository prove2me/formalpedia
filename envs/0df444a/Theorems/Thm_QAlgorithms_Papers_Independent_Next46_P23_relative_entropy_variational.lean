-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_relative_entropy_variational
-- name    : QAlgorithms.Papers.Independent.Next46.P23.relative_entropy_variational
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:59:20.037096+00:00
-- url     : https://prove2.me/theorems/6cb21eeb-044d-4d30-815a-beb0c7d9a22a
-- title:
--   Theorem 2.15
-- statement:
--   Let $\rho,\nu$ be normalized states on a nonzero finite-dimensional complex Hilbert space. Use signed relative entropy and the exponential compressed to the support of $\nu$. Then $$S(\rho\mid\nu)=\inf_{A=A^*}\{\log\operatorname{tr}(e^{A+\log\nu})-\rho(A)\},\quad \log\operatorname{tr}(e^{A+\log\nu})=\max_\rho\{S(\rho\mid\nu)+\rho(A)\}.$$ The second maximizer is uniquely the normalized compressed exponential. For equal supports the first infimum is attained, with equality exactly when the support compression of $A$ is $\log\rho-\log\nu$ up to a real scalar on the support. Failed support inclusion retains $-\infty$.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 47, Theorem 2.15

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Theorem2.15 and its Remark, source PDF p.47, using the compressed exponential. -/
theorem relative_entropy_variational [Nonempty I] :
    (∀ rho nu : Mat I, QAlgorithms.IsDensityMatrix rho → QAlgorithms.IsDensityMatrix nu →
      signedRelativeEntropy rho nu = sInf {v | ∃ A : Mat I, A.IsHermitian ∧
        v = ((Real.log ((compressedExp A nu).trace.re) - ev rho A : ℝ) : EReal)} ∧
      (support rho = support nu →
        (∃ A : Mat I, A.IsHermitian ∧ signedRelativeEntropy rho nu =
          ((Real.log ((compressedExp A nu).trace.re) - ev rho A : ℝ) : EReal)) ∧
        (∀ A : Mat I, A.IsHermitian →
          (signedRelativeEntropy rho nu = ((Real.log ((compressedExp A nu).trace.re) - ev rho A : ℝ) : EReal) ↔
            ∃ c : ℝ, support nu * A * support nu =
              logMat rho - logMat nu + (c : ℂ) • support nu)))) ∧
    (∀ A nu : Mat I, A.IsHermitian → QAlgorithms.IsDensityMatrix nu →
      let rhoMax := ((compressedExp A nu).trace)⁻¹ • compressedExp A nu
      QAlgorithms.IsDensityMatrix rhoMax ∧
      (∀ rho : Mat I, QAlgorithms.IsDensityMatrix rho →
        signedRelativeEntropy rho nu + (ev rho A : EReal) ≤ (Real.log ((compressedExp A nu).trace.re) : EReal) ∧
        (signedRelativeEntropy rho nu + (ev rho A : EReal) =
          (Real.log ((compressedExp A nu).trace.re) : EReal) ↔ rho = rhoMax))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
