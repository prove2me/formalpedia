-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P02_zeroTrustedNoise
-- name    : QAlgorithms.Papers.Independent.Intake100.P02.zeroTrustedNoise
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-30T11:49:19.865363+00:00
-- url     : https://prove2.me/theorems/2c2f7a2a-f792-41c8-b922-5ae2d5fbb1f5
-- title:
--   Zero trusted noise recovers half the reverse-information expression
-- statement:
--   Let $0<\eta<1$ be thermal-loss transmissivity and let $\omega\ge 1/2$ be the environmental quadrature variance, with vacuum variance $1/2$. Define $s(x)=(x+1/2)\log_2(x+1/2)-(x-1/2)\log_2(x-1/2)$, continuously at $x=1/2$. Write $R(\eta,\omega,\xi)$ for the signed calculated expression in Eq. (116), including its basis-sifting factor, and $R_{\rm LB}(\eta,\omega)=-\log_2(1-\eta)-s(\omega)$. Then
--
--   $$R(\eta,\omega,0)=\frac12 R_{\rm LB}(\eta,\omega).$$
--
--   This identifies the zero-trusted-noise specialization of the calculated rate. It does not identify an operational capacity or assert finite-modulation achievability.
-- source:
--   Theory of channel simulation and bounds for private communication, arXiv:1711.09909v3, PDF p. 15, Remark 9: zero trusted noise recovers the reverse coherent rate

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P02

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P02

open Filter MeasureTheory QAlgorithms

open scoped ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal)

/-- arXiv:1711.09909v3, PDF p.15, Remark 9: zero trusted noise in the
calculated (116) recovers half of (110). This is a signed-rate identity. -/
theorem zeroTrustedNoise (eta omega : ℝ)
    (heta_positive : 0 < eta) (heta_lt_one : eta < 1)
    (homega : 1 / 2 ≤ omega) :
    siftedRateExpression eta omega 0 = reverseRateExpression eta omega / 2 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P02

end
