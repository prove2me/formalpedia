-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_filtered_relativeEntropy
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.filtered_relativeEntropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:38:58.588214+00:00
-- url     : https://prove2.me/theorems/60c9e02f-94de-406d-97ce-7d9d9bef5fad
-- title:
--   Filtered relative-entropy estimate on the positive-denominator domain
-- statement:
--   Let $\rho,\sigma$ be density operators on a nonzero finite-dimensional space of dimension $d$, with $\operatorname{supp}\rho\subseteq\operatorname{supp}\sigma$. Let $0\le\delta<1/4$, set $\delta'=2\sqrt\delta$, and let $0\le P\le1$ satisfy $\operatorname{Tr}P\rho\ge1-\delta$. Put $\tau=\sqrt P\rho\sqrt P$ and
--
--   $$S_1^P(\rho\Vert\sigma)=\frac{\operatorname{Tr}(\sqrt P\rho\log_2\rho\sqrt P\Pi_\sigma-\tau\log_2\sigma)}{\operatorname{Tr}(\tau\Pi_\sigma)}.$$
--
--   The denominator is strictly positive and
--
--   $$S_1^P(\rho\Vert\sigma)\le\frac{D(\tau\Vert\sigma)+2\delta'\log_2d+2}{1-\delta'}.$$
--
--   Relative entropy is extended by $+\infty$ on support failure. This controls the explicit filtered logarithmic-derivative ratio used in the converse.
--
--   **Source correction.** The printed domain $\delta\ge0$ is restricted to $\delta<1/4$ to justify the proof's division by $1-\delta'$. The explicit ratio (28), used in (40), is retained without the source's invalid identification with a two-sided order-one limit.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 12, Lemma 13, filtered relative-entropy estimate

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

/-- Lemma 13, PDF p.12, (39), read via the explicit ratio (28).
SOURCE CORRECTION: printed delta>=0 is restricted to 0<=delta<1/4,
the positive-denominator domain required by (42)–(43). Denominator positivity
is a conclusion, not an assumed proof intermediate. -/
theorem filtered_relativeEntropy {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (rho sigma P : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportIncluded rho sigma) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hsmall : delta < 1/4) (hP : Accept rho P delta) :
    0 < filterDenom rho sigma P ∧
    (filteredOne rho sigma P : EReal) ≤
      (relativeD (effectFilteredState rho P) sigma +
        ((2 * (2 * Real.sqrt delta) * Real.logb 2 (Fintype.card I) + 2 : ℝ) : EReal)) *
        ((1 / (1 - 2 * Real.sqrt delta) : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
