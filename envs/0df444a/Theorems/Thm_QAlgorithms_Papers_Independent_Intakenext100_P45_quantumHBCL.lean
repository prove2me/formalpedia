-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P45_quantumHBCL
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P45.quantumHBCL
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:18:53.116207+00:00
-- url     : https://prove2.me/theorems/c7e1252d-3057-4639-bb4a-9dc5a6a1b5a8
-- title:
--   Theorem 5, Quantum HBCL
-- statement:
--   For arbitrary finite-dimensional density operators $\rho,\sigma$ and every $r>0$, there is a sequence of joint orthogonal test projections on IID copies whose two extended error-rate limits exist and satisfy
--
--   $$\alpha_R=e_Q(r),\qquad\beta_R\ge r.$$
--
--   For any sequence of orthogonal test projections with both limits, $\beta_R>r$ implies $\alpha_R\le e_Q(r)$. Singular and orthogonal states and infinite exponents are included. The theorem retains the stated weak bound on $\beta_R$, without the unjustified equality asserted at the end of its proof.
-- source:
--   Asymptotic Error Rates in Quantum Hypothesis Testing, arXiv:0708.4282v1, PDF p. 27, Theorem 5, Quantum HBCL

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

/-- arXiv:0708.4282v1, PDF pp.27,28,29,30: Theorem 5, Quantum HBCL. -/
theorem quantumHBCL (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    (∀ r : ℝ, 0 < r → ∃ P : QuantumTests I, ∃ b : EReal,
      (∀ k, IsProjection (P k)) ∧ HasRate (quantumAlpha rho P) (quantumExponent rho sigma r) ∧
      HasRate (quantumBeta sigma P) b ∧ (r : EReal) ≤ b) ∧
    (∀ (P : QuantumTests I) (a b : EReal) (r : ℝ),
      (∀ k, IsProjection (P k)) → 0 < r → HasRate (quantumAlpha rho P) a →
      HasRate (quantumBeta sigma P) b → (r : EReal) < b → a ≤ quantumExponent rho sigma r) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P45

end
