-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P14_highLoss_boundCurves
-- name    : QAlgorithms.Papers.Independent.Gap20.P14.highLoss_boundCurves
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T20:32:25.863726+00:00
-- url     : https://prove2.me/theorems/58dc7390-a1c0-440e-b536-41c2f74178c7
-- title:
--   First-order high-loss limits of the upper and lower curves
-- statement:
--   For $0<\eta<1$, let $U(\eta)=\log_2((1+\eta)/(1-\eta))$ be the upper-bound curve and let $L(\eta)=-\log_2(1-\eta)$ be the cited lower-bound curve. Then
--
--   $$
--   \lim_{\eta\downarrow0}\frac{U(\eta)}{\eta}=\frac{2}{\ln2},\qquad
--   \lim_{\eta\downarrow0}\frac{L(\eta)}{\eta}=\frac{1}{\ln2}.
--   $$
--
--   These limits give the linear approximations of the two curves at high loss. They do not identify a first-order coefficient for the operational secret-key capacity.
-- source:
--   Fundamental rate-loss tradeoff for optical quantum key distribution, arXiv:1504.06390v1, PDF p. 6, Unnumbered: high-loss asymptotics of upper and lower curves

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P14

open Filter

open QAlgorithms

open QAlgorithms.Papers.Independent.Claimed50.P12 (squashedEntanglement)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1504.06390v1, PDF p.6 (the discussion following Eq.(7) on p.5):
the two bound curves have distinct first-order coefficients at high loss.
These are limits of the bounds, not an exact coefficient for capacity. -/
theorem highLoss_boundCurves :
    Tendsto (fun eta : ℝ => rateLossCurve eta / eta)
      (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)) (nhds (2 / Real.log 2)) ∧
    Tendsto (fun eta : ℝ => reverseCoherentCurve eta / eta)
      (nhdsWithin 0 (Set.Ioo (0 : ℝ) 1)) (nhds (1 / Real.log 2)) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P14

end
