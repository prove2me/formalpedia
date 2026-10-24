-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P17_minimumEigenvalueSeparation
-- name    : QAlgorithms.Papers.Independent.Support50.P17.minimumEigenvalueSeparation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:00:09.360155+00:00
-- url     : https://prove2.me/theorems/d8adc30a-8ce6-4c85-ab36-ea1a0aeeaf5b
-- title:
--   Minimum eigenvalues cannot separate faster than trace distance
-- statement:
--   Let $A,B\ge0$ be matrices on the same nonzero finite-dimensional complex Hilbert space, with $\operatorname{Tr}A=\operatorname{Tr}B$. Let $\alpha=\lambda_{\min}(A)$ and $\beta=\lambda_{\min}(B)$ denote their full smallest eigenvalues, including any zero eigenvalues. For $T=\tfrac12\|A-B\|_1$, where $\|X\|_1=\operatorname{Tr}\sqrt{X^*X}$, one has
--
--   $$
--   T\ge|\alpha-\beta|.
--   $$
--
--   No trace-one normalization is imposed. This supplies the eigenvalue-distance constraint needed in the entropy bounds.
-- source:
--   Continuity bounds on the quantum relative entropy - II, arXiv:1105.2656v3, PDF p. 6, Lemma 2: minimum-eigenvalue separation

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P17

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Support50.P17

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the exact frozen support predicate and signed, unnormalised entropy.

open QAlgorithms.Papers.Independent.Dependency50.P21 (IsSupported relativeEntropy)

/-- PDF p.6, Lemma 2: separation of the full minimum eigenvalues for equal-trace
PSD matrices, including zero eigenvalues and the one-dimensional case. -/
theorem minimumEigenvalueSeparation {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (A B : Matrix I I ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace = B.trace) :
    |minEigenvalue A - minEigenvalue B| ≤ traceDistance A B := by sorry

end QAlgorithms.Papers.Independent.Support50.P17

end
