-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_traceNorm_weighted
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.traceNorm_weighted
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:33:10.326096+00:00
-- url     : https://prove2.me/theorems/43f017d7-bafc-480d-bb4a-de36105b3b91
-- title:
--   Trace norm and weighted quadratic bounds
-- statement:
--   Let $X$ be self-adjoint on a nonzero finite-dimensional complex Hilbert space, and let $\xi$ be positive definite. With $\|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}$,
--
--   $$\|X\|_1^2\le\operatorname{Tr}(\xi)\operatorname{Tr}(X\xi^{-1/2}X\xi^{-1/2})\le\operatorname{Tr}(\xi)\operatorname{Tr}(X^2\xi^{-1}).$$
--
--   Positive definiteness makes the inverse powers genuine inverses. The first inequality is credited to Renner in the source; this paper supplies the second inequality. The chain controls trace distance by weighted quadratic quantities.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 2, Lemma 3, trace-norm and weighted quadratic bounds

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Advance50.P07

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD petzD)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative Density elog)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P19 (marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Support50.P21 (PositiveTensorBasis)

/-- Lemma 3, PDF pp.2–3, (5). Strict positive definiteness excludes
kernel-inverse defaults. The first inequality is credited to [18]. -/
theorem traceNorm_weighted {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (X xi : Mat I) (hX : X.IsHermitian) (hxi : xi.PosDef) :
    traceNorm X ^ 2 ≤ xi.trace.re * (X * supportPower xi (-1/2 : ℝ) *
      X * supportPower xi (-1/2 : ℝ)).trace.re ∧
    xi.trace.re * (X * supportPower xi (-1/2 : ℝ) * X * supportPower xi (-1/2 : ℝ)).trace.re ≤
      xi.trace.re * (X ^ 2 * supportPower xi (-1 : ℝ)).trace.re := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
