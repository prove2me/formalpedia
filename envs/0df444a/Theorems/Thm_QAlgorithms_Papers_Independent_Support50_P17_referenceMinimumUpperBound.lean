-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_referenceMinimumUpperBound
-- name    : QAlgorithms.Papers.Independent.Support50.P17.referenceMinimumUpperBound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:03:35.016405+00:00
-- url     : https://prove2.me/theorems/50e9d194-cf54-46d8-95ec-7c79012479aa
-- title:
--   Relative entropy bound using only the reference minimum
-- statement:
--   Let $\rho,\sigma$ be density matrices on the same nonzero finite-dimensional complex Hilbert space, and suppose $\beta=\lambda_{\min}(\sigma)>0$. Write $T=\tfrac12\|\rho-\sigma\|_1$. Then
--
--   $$
--   T\le\beta\ \Longrightarrow\ S(\rho\|\sigma)\le(\beta+T)\log(1+T/\beta)+(\beta-T)\log(1-T/\beta),
--   $$
--
--   and
--
--   $$
--   T\ge\beta\ \Longrightarrow\ S(\rho\|\sigma)\le(\beta+T)\log(1+T/\beta).
--   $$
--
--   At $T=\beta$ the zero-weight logarithmic term is zero and both formulas apply. No positive lower bound on $\lambda_{\min}(\rho)$ is assumed.
--
--   This is the paper's corrected rederivation of the earlier reference-minimum bound. The positive-$\beta$ domain is inherited from Theorem 1 and the scaling proof.
-- source:
--   Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, PDF p. 9, Corollary 1: upper bound knowing only the reference minimum (19)–(20)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact frozen support predicate and signed, unnormalised entropy.

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

/-- PDF p.9, Corollary 1, (19)–(20): only the reference minimum is given.
The beta>0 domain comes from Theorem 1 and its scaling proof. At T=beta both
branches apply and the vanishing logarithmic weight contributes zero. -/
theorem referenceMinimumUpperBound {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hbeta : 0 < minEigenvalue sigma) :
    let beta := minEigenvalue sigma
    let T := traceDistance rho sigma
    (T ≤ beta → relativeEntropy rho sigma ≤
      (((beta + T) * Real.log (1 + T / beta) +
        (beta - T) * Real.log (1 - T / beta) : ℝ) : EReal)) ∧
    (beta ≤ T → relativeEntropy rho sigma ≤
      (((beta + T) * Real.log (1 + T / beta) : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end
