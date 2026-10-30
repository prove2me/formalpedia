-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_psi_convex
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.psi_convex
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T08:37:24.026986+00:00
-- url     : https://prove2.me/theorems/079e24e2-6912-4346-aa01-2e31ee0255fb
-- title:
--   Convexity of the log quasi-entropy moment
-- statement:
--   Let $\rho,\sigma\ge0$ and $0\le P\le1$ act on a nonzero finite-dimensional Hilbert space. Assume the trace below is strictly positive for every $\alpha>0$, as in the preceding paragraph of VI.B.2. With spectral powers supported on the operators' supports, define
--
--   $$\psi_\alpha^P(\rho\Vert\sigma)=\log_2\operatorname{Tr}(\sqrt P\rho^\alpha\sqrt P\sigma^{1-\alpha}).$$
--
--   The real-valued function $\alpha\mapsto\psi_\alpha^P(\rho\Vert\sigma)$ is convex on $(0,\infty)$. No trace normalization is required. This supplies the convex log-moment object used in the paper's entropy analysis.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 6, Lemma 8, convexity of the log quasi-entropy moment

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

/-- Lemma 8, PDF pp.6–7. The preceding paragraph's nonorthogonality
assumption is strict positivity of every moment on alpha>0. -/
theorem psi_convex {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma P : Mat I) (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef)
    (hP : IsEffect P) (hfinite : ∀ alpha : ℝ, 0 < alpha → 0 < quasiMoment rho sigma P alpha) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (quasiLogMoment rho sigma P) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
