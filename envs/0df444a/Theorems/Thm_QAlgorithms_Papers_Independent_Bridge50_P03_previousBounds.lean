-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P03_previousBounds
-- name    : QAlgorithms.Papers.Independent.Bridge50.P03.previousBounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:52:42.513231+00:00
-- url     : https://prove2.me/theorems/b463120c-4d1b-4953-b5a0-561eedc3d010
-- title:
--   Optimized detector rate weakly dominates both earlier bounds
-- statement:
--   Let $0\le\eta<1$ be the channel transmissivity and let $1\le\omega<\infty$ be the environment quadrature variance, with vacuum variance one. All logarithms and rates are in bits. Define the thermal entropy
--   $$h(x)=\frac{x+1}{2}\log_2\frac{x+1}{2}-\frac{x-1}{2}\log_2\frac{x-1}{2},\qquad x\ge1,$$
--   with $0\log_2 0=0$. For detector transmissivity $d\in[0,1]$ and finite trusted thermal variance $\gamma\ge1$, write
--   $$R(\eta,\omega,d,\gamma)=\frac12\log_2\frac{d\omega+(1-d)(1-\eta)\gamma}{(1-\eta)[d(1-\eta)\omega+(1-d)\gamma]}+h\!\left(\sqrt{\frac{\omega[d+(1-\eta)(1-d)\omega\gamma]}{d\omega+(1-\eta)(1-d)\gamma}}\right)-h(\omega).$$
--   At $d=0$ this expression is zero. The symbol $R$ denotes the signed expression, so a negative value is not asserted to be a positive achievable key yield.
--
--   Set $A(\eta,\omega)=-\log_2(1-\eta)-h(\omega)$ and define the balanced-vacuum curve by
--   $$B(\eta,\omega)=\frac12\log_2\frac{\omega+1-\eta}{(1-\eta)[(1-\eta)\omega+1]}+h\!\left(\sqrt{\frac{\omega[1+(1-\eta)\omega]}{\omega+1-\eta}}\right)-h(\omega).$$
--   The admissible detector rates have an attained largest value
--   $$R_M(\eta,\omega)=\max_{0\le d\le1,\ \gamma\ge1}R(\eta,\omega,d,\gamma).$$
--   It satisfies
--   $$R_M(\eta,\omega)\ge\max\{0,A(\eta,\omega),B(\eta,\omega)\}.$$
--   Thus the optimization includes both earlier signed lower-bound curves and the option to abort. Dominance is weak, allowing equality, including vacuum loss.
-- source:
--   Secret key capacity of the thermal-loss channel: Improving the lower bound, arXiv:1609.02169v1, PDF p. 7, Section 4, discussion after Eq. (36)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P03

/-- arXiv:1609.02169v1, PDF pp.7--8, Section 4: optimization includes
both earlier comparison curves. IsGreatest preserves actual attainment
of (22), and the disconnected detector supplies the nonnegative branch.
Dominance is weak; in particular equality is allowed for vacuum loss. -/
theorem previousBounds (eta omega : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (homega : 1 ≤ omega) :
    IsGreatest (detectorRateImage eta omega) (optimizedDetectorRate eta omega) ∧
    0 ≤ optimizedDetectorRate eta omega ∧
    reverseInformationCurve eta omega ≤ optimizedDetectorRate eta omega ∧
    balancedVacuumCurve eta omega ≤ optimizedDetectorRate eta omega := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P03

end
