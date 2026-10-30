-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P03_strictImprovement
-- name    : QAlgorithms.Papers.Independent.Bridge50.P03.strictImprovement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:53:13.398456+00:00
-- url     : https://prove2.me/theorems/29a157e3-cfcd-40ea-87f5-162182de3385
-- title:
--   Strict improvement for some one-photon thermal-loss channel
-- statement:
--   Let $0\le\eta<1$ be the channel transmissivity and let $1\le\omega<\infty$ be the environment quadrature variance, with vacuum variance one. All logarithms and rates are in bits. Define the thermal entropy
--   $$h(x)=\frac{x+1}{2}\log_2\frac{x+1}{2}-\frac{x-1}{2}\log_2\frac{x-1}{2},\qquad x\ge1,$$
--   with $0\log_2 0=0$. For detector transmissivity $d\in[0,1]$ and finite trusted thermal variance $\gamma\ge1$, write
--   $$R(\eta,\omega,d,\gamma)=\frac12\log_2\frac{d\omega+(1-d)(1-\eta)\gamma}{(1-\eta)[d(1-\eta)\omega+(1-d)\gamma]}+h\!\left(\sqrt{\frac{\omega[d+(1-\eta)(1-d)\omega\gamma]}{d\omega+(1-\eta)(1-d)\gamma}}\right)-h(\omega).$$
--   At $d=0$ this expression is zero. The symbol $R$ denotes the signed expression, so a negative value is not asserted to be a positive achievable key yield.
--
--   For the one-photon environment, $\omega=3$. Let $A(\eta,\omega)=-\log_2(1-\eta)-h(\omega)$ and let
--   $$B(\eta,\omega)=\frac12\log_2\frac{\omega+1-\eta}{(1-\eta)[(1-\eta)\omega+1]}+h\!\left(\sqrt{\frac{\omega[1+(1-\eta)\omega]}{\omega+1-\eta}}\right)-h(\omega).$$
--   There exists $\eta\in(0,1)$ for which the detector rates have an attained maximum $R_M(\eta,3)$ and
--   $$R_M(\eta,3)>\max\{0,A(\eta,3),B(\eta,3)\}.$$
--   This is the existential strict separation illustrated in Figure 2 and asserted in the conclusion. It does not assert strict improvement at every channel parameter or specify an exact numerical optimizer.
-- source:
--   Secret key capacity of the thermal-loss channel: Improving the lower bound, arXiv:1609.02169v1, PDF p. 8, Figure 2 and Section 5

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P03

/-- arXiv:1609.02169v1, PDF p.8, Figure 2 and Section 5: some channel
transmissivity at omega=3 (one thermal photon) gives a positive optimized
rate strictly above both previous bounds. No numerical witness or universal
strictness is claimed. IsGreatest makes the optimized value an attained max. -/
theorem strictImprovement :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      IsGreatest (detectorRateImage eta 3) (optimizedDetectorRate eta 3) ∧
      max 0 (max (reverseInformationCurve eta 3) (balancedVacuumCurve eta 3)) <
        optimizedDetectorRate eta 3 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P03

end
