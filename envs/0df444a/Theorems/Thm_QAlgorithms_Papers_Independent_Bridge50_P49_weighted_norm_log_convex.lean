-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P49_weighted_norm_log_convex
-- name    : QAlgorithms.Papers.Independent.Bridge50.P49.weighted_norm_log_convex
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:19:58.489978+00:00
-- url     : https://prove2.me/theorems/23b218b9-7a8f-4a31-af39-788e59800e15
-- title:
--   Log-convexity of weighted Schatten norms
-- statement:
--   Let $\mathcal H$ be finite dimensional, $\sigma>0$, and $X\in\mathcal L(\mathcal H)$ be arbitrary. Let $1\leq p_0<p_1\leq\infty$ and $0<\theta<1$, and define $1/p_\theta=(1-\theta)/p_0+\theta/p_1$, with $1/\infty=0$. For $\|X\|_{p,\sigma}=\|\sigma^{1/(2p)}X\sigma^{1/(2p)}\|_p$,
--
--   $$\|X\|_{p_\theta,\sigma}\leq\|X\|_{p_0,\sigma}^{1-\theta}\|X\|_{p_1,\sigma}^{\theta}.$$
--
--   This is the constant-function specialization of weighted interpolation. The strict inequality between the two endpoint orders is retained.
-- source:
--   Sandwiched Rényi Divergence Satisfies Data Processing Inequality, arXiv:1306.5920v6, PDF p. 6, Corollary 3: log-convexity of weighted Schatten norms

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

/-- Beigi, arXiv:1306.5920v6, Corollary 3, PDF p.6: all X, with strict p0 < p1. -/
theorem weighted_norm_log_convex {I : Type} [Fintype I] [DecidableEq I]
    (p0 p1 : ℝ≥0∞) (hp0 : 1 ≤ p0) (hp01 : p0 < p1)
    (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (sigma X : Mat I) (hsigma : sigma.PosDef) :
    beigiWeightedSchattenNorm (interpolatedOrder p0 p1 theta) sigma X ≤
      beigiWeightedSchattenNorm p0 sigma X ^ (1 - theta) * beigiWeightedSchattenNorm p1 sigma X ^ theta := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P49

end
