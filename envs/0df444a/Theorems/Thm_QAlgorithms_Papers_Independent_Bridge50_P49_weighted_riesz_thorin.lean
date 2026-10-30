-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P49_weighted_riesz_thorin
-- name    : QAlgorithms.Papers.Independent.Bridge50.P49.weighted_riesz_thorin
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:20:50.133536+00:00
-- url     : https://prove2.me/theorems/7e22ae7d-4567-4d88-8437-fcd4c659eabf
-- title:
--   Riesz–Thorin interpolation for weighted matrix spaces
-- statement:
--   Let $\Phi:\mathcal L(\mathcal H)\to\mathcal L(\mathcal H')$ be complex linear between finite-dimensional matrix spaces, and let $\sigma>0$ and $\sigma'>0$ be weights on the two spaces. Let $1\leq p_0\leq p_1\leq\infty$, $1\leq q_0\leq q_1\leq\infty$, and $0\leq\theta\leq1$. Interpolate each reciprocal order by $1/p_\theta=(1-\theta)/p_0+\theta/p_1$ and the analogous formula for $q_\theta$. Define $\|X\|_{p,\sigma}=\|\sigma^{1/(2p)}X\sigma^{1/(2p)}\|_p$ and the induced norm $\|\Phi\|_{(p,\sigma)\to(q,\sigma')}=\sup_{X\ne0}\|\Phi(X)\|_{q,\sigma'}/\|X\|_{p,\sigma}$. Then
--
--   $$\|\Phi\|_{(p_\theta,\sigma)\to(q_\theta,\sigma')}\leq\|\Phi\|_{(p_0,\sigma)\to(q_0,\sigma')}^{1-\theta}\|\Phi\|_{(p_1,\sigma)\to(q_1,\sigma')}^{\theta}.$$
--
--   This bounds arbitrary linear superoperators; positivity and trace preservation are not required.
-- source:
--   Sandwiched Rényi Divergence Satisfies Data Processing Inequality, arXiv:1306.5920v6, PDF p. 7, Theorem 4 (Riesz-Thorin theorem for L_(p,σ) spaces)

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

/-- Beigi, arXiv:1306.5920v6, Theorem 4, PDF pp.6--7: weighted Riesz--Thorin.
Phi is any complex-linear map; no positivity or channel assumption is imposed. -/
theorem weighted_riesz_thorin {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (Phi : Mat I →ₗ[ℂ] Mat J)
    (p0 p1 q0 q1 : ℝ≥0∞) (hp0 : 1 ≤ p0) (hp01 : p0 ≤ p1)
    (hq0 : 1 ≤ q0) (hq01 : q0 ≤ q1) (theta : ℝ)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (sigma : Mat I) (tau : Mat J) (hsigma : sigma.PosDef) (htau : tau.PosDef) :
    weightedMapNorm (interpolatedOrder p0 p1 theta) (interpolatedOrder q0 q1 theta)
        sigma tau Phi ≤
      weightedMapNorm p0 q0 sigma tau Phi ^ (1 - theta) *
        weightedMapNorm p1 q1 sigma tau Phi ^ theta := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P49

end
