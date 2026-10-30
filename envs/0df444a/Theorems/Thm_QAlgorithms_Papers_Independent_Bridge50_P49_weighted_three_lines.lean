-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P49_weighted_three_lines
-- name    : QAlgorithms.Papers.Independent.Bridge50.P49.weighted_three_lines
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:19:17.404227+00:00
-- url     : https://prove2.me/theorems/cabb681c-0f5f-4cc8-b02f-d1bb843eb999
-- title:
--   Weighted matrix-valued three-lines theorem
-- statement:
--   Let $\mathcal H$ be finite dimensional, let $\sigma>0$ be an operator on $\mathcal H$, and let $F:S\to\mathcal L(\mathcal H)$ be entrywise bounded and holomorphic in the interior of the closed strip $S=\{z:0\leq\operatorname{Re}z\leq1\}$, with continuity from $S$ at its boundary. For $1\leq p_0\leq p_1\leq\infty$ and $0<\theta<1$, define $1/p_\theta=(1-\theta)/p_0+\theta/p_1$, using $1/\infty=0$. Write $\|X\|_{p,\sigma}=\|\sigma^{1/(2p)}X\sigma^{1/(2p)}\|_p$, where the infinite-order norm is the operator norm, and set $M_k=\sup_{t\in\mathbb R}\|F(k+it)\|_{p_k,\sigma}$. Then
--
--   $$\|F(\theta)\|_{p_\theta,\sigma}\leq M_0^{1-\theta}M_1^\theta.$$
--
--   This interpolates weighted matrix norms without a positivity assumption on $F$ or a trace normalization on $\sigma$.
-- source:
--   Sandwiched Rényi Divergence Satisfies Data Processing Inequality, arXiv:1306.5920v6, PDF p. 5, Theorem 2: weighted matrix-valued three-line theorem

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P49

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Bridge50.P49

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Dependency50.P35
  (spectralPower Dominates rawTrace leftMarginal rightMarginal marginalAB marginalAC)

/-- Beigi, arXiv:1306.5920v6, Theorem 2, PDF pp.5--6: weighted matrix three-lines.
The proof's last line on p.6 has a repeated exponent typo; the theorem uses theta. -/
theorem weighted_three_lines {I : Type} [Fintype I] [DecidableEq I]
    (F : ℂ → Mat I) (hbounded : StripBounded F) (hregular : StripRegular F)
    (sigma : Mat I) (hsigma : sigma.PosDef) (p0 p1 : ℝ≥0∞)
    (hp0 : 1 ≤ p0) (hp01 : p0 ≤ p1) (theta : ℝ)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    beigiWeightedSchattenNorm (interpolatedOrder p0 p1 theta) sigma (F (theta : ℂ)) ≤
      boundaryNorm F p0 sigma 0 ^ (1 - theta) * boundaryNorm F p1 sigma 1 ^ theta := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P49

end
