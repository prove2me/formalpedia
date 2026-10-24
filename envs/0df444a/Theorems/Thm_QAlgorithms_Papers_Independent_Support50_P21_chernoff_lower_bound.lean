-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_chernoff_lower_bound
-- name    : QAlgorithms.Papers.Independent.Support50.P21.chernoff_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T20:51:16.012128+00:00
-- url     : https://prove2.me/theorems/ec96b9a9-191c-4152-9cc5-25d551e4644f
-- title:
--   §IV: min-relative entropy lower bounds the quantum Chernoff distance
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   For density operators $\rho,\sigma$, define $q(s)=\operatorname{Tr}(\rho^s\sigma^{1-s})$ on $0\le s\le1$, taking a zero power as the support projector. The minimum is attained, and the Chernoff distance obeys
--
--   $$\xi(\rho,\sigma):=-\log_2\min_{0\le s\le1}q(s)\ge D_{\min}(\rho\Vert\sigma).$$
--
--   The endpoint convention is the continuous support-limit extension; zero minimum gives $+\infty$. This asserts the paper's lower bound, without a separate operational exponent theorem.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 6, §IV: min-relative entropy lower bounds the quantum Chernoff distance

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P21

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Use the accepted declarations directly; no paper-local aliases hide dimension binders.

open QAlgorithms.Papers.Independent.Claimed50.P33
  (FiniteState IsAverageLocalMonotone IsAdaptiveLOCCMonotone)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

section Statements

variable [Nonempty I] [Nonempty J]

/-- PDF p.6: only the lower bound on Chernoff distance, plus attainment of the
printed minimum. Support-power endpoints give the continuous extension. -/
theorem chernoff_lower_bound (rho sigma : Mat I)
    (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    dMin rho sigma ≤ chernoff rho sigma ∧
    ∃ s ∈ Set.Icc (0 : ℝ) 1,
      IsLeast (chernoffCoefficient rho sigma '' Set.Icc (0 : ℝ) 1)
        (chernoffCoefficient rho sigma s) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
