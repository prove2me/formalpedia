-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P21_zero_smoothing
-- name    : QAlgorithms.Papers.Independent.Support50.P21.zero_smoothing
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T20:52:03.132143+00:00
-- url     : https://prove2.me/theorems/f4bba76a-3614-45a0-9735-b8530a043cb4
-- title:
--   §VI: zero smoothing recovers the original divergences
-- statement:
--   All systems are nonzero finite-dimensional complex Hilbert spaces, and logarithms have base two.
--
--   For a density operator $\rho$ and a positive operator $\sigma$, smoothing with the full trace-norm, trace-capped ball satisfies
--
--   $$D_{\min}^{0}(\rho\Vert\sigma)=D_{\min}(\rho\Vert\sigma),\qquad D_{\max}^{0}(\rho\Vert\sigma)=D_{\max}(\rho\Vert\sigma).$$
--
--   The zero-radius ball contains exactly $\rho$. This recovers the unsmoothed quantities without normalizing $\sigma$.
-- source:
--   Min- and Max- Relative Entropies and a New Entanglement Monotone, arXiv:0803.2770v3, PDF p. 7, §VI: zero smoothing recovers the original divergences

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

/-- PDF p.7, before Definition 4: zero smoothing recovers both divergences.
The comparison sigma is positive, not necessarily normalized. -/
theorem zero_smoothing (rho sigma : Mat I) (hrho : IsDensityMatrix rho)
    (hsigma : sigma.PosSemidef) :
    traceSmoothMin 0 rho sigma = dMin rho sigma ∧ traceSmoothMax 0 rho sigma = maxRelative rho sigma := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P21

end
