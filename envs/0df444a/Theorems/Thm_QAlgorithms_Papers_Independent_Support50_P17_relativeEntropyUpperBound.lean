-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_relativeEntropyUpperBound
-- name    : QAlgorithms.Papers.Independent.Support50.P17.relativeEntropyUpperBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:02:47.641765+00:00
-- url     : https://prove2.me/theorems/0632e71b-9f55-4af3-8164-250df64f7672
-- title:
--   Relative entropy bound using both smallest eigenvalues
-- statement:
--   Let $\rho,\sigma$ be density matrices on the same nonzero finite-dimensional complex Hilbert space. Put $\alpha=\lambda_{\min}(\rho)$, $\beta=\lambda_{\min}(\sigma)$ and $T=\tfrac12\|\rho-\sigma\|_1$. Always,
--
--   $$
--   T\ge|\alpha-\beta|.
--   $$
--
--   If $\beta>0$, then, with $q(0,T)=0$ and $q(\alpha,T)=-\alpha\log(1+T/\alpha)$ for $\alpha>0$,
--
--   $$
--   S(\rho\|\sigma)\le(\beta+T)\log(1+T/\beta)+q(\alpha,T).
--   $$
--
--   Thus the positive-$\alpha$ formula (17) and the singular-$\rho$ extension (18) are both retained. The separation statement includes singular $\sigma$; no finite entropy bound is asserted when $\beta=0$.
--
--   This is the main continuity bound advertised in the abstract. The separate dimensional-necessity remark is not included.
-- source:
--   Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, PDF p. 8, Theorem 1: upper bound with both minimum eigenvalues (17)–(18)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact frozen support predicate and signed, unnormalised entropy.

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

/-- PDF p.8, Theorem 1, (17)–(18): both minimum eigenvalues are computed from
the densities. Separation also holds for singular sigma. The finite entropy bound
retains beta>0 and includes singular rho through the zero-alpha correction. -/
theorem relativeEntropyUpperBound {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    let alpha := minEigenvalue rho
    let beta := minEigenvalue sigma
    let T := traceDistance rho sigma
    |alpha - beta| ≤ T ∧
      (0 < beta → relativeEntropy rho sigma ≤
        (((beta + T) * Real.log (1 + T / beta) +
          zeroExtendedLogCorrection alpha T : ℝ) : EReal)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end
