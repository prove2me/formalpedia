-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P03_noTrustedNoise
-- name    : QAlgorithms.Papers.Independent.Bridge50.P03.noTrustedNoise
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:51:39.97379+00:00
-- url     : https://prove2.me/theorems/20f1c020-b7c7-4e61-a24e-9868401b7a85
-- title:
--   No trusted detector noise recovers the reverse-information curve
-- statement:
--   Let $0\le\eta<1$ be the channel transmissivity and let $1\le\omega<\infty$ be the environment quadrature variance, with vacuum variance one. All logarithms and rates are in bits. Define the thermal entropy
--   $$h(x)=\frac{x+1}{2}\log_2\frac{x+1}{2}-\frac{x-1}{2}\log_2\frac{x-1}{2},\qquad x\ge1,$$
--   with $0\log_2 0=0$. For detector transmissivity $d\in[0,1]$ and finite trusted thermal variance $\gamma\ge1$, write
--   $$R(\eta,\omega,d,\gamma)=\frac12\log_2\frac{d\omega+(1-d)(1-\eta)\gamma}{(1-\eta)[d(1-\eta)\omega+(1-d)\gamma]}+h\!\left(\sqrt{\frac{\omega[d+(1-\eta)(1-d)\omega\gamma]}{d\omega+(1-\eta)(1-d)\gamma}}\right)-h(\omega).$$
--   At $d=0$ this expression is zero. The symbol $R$ denotes the signed expression, so a negative value is not asserted to be a positive achievable key yield.
--
--   For every finite $\gamma\ge1$, no trusted detector noise gives
--   $$R(\eta,\omega,1,\gamma)=-\log_2(1-\eta)-h(\omega).$$
--   This identifies the earlier reverse-coherent-information comparison curve inside the new detector family. The auxiliary variance disappears because the unused detector port decouples.
-- source:
--   Secret key capacity of the thermal-loss channel: Improving the lower bound, arXiv:1609.02169v1, PDF p. 7, Section 4, after Eq. (36)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P03

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P03

/-- arXiv:1609.02169v1, PDF p.7, Section 4, following (36): no trusted
noise at Bob recovers the signed reverse coherent-information expression.
Gamma disappears when the unused auxiliary detector port decouples. -/
theorem noTrustedNoise (eta omega gamma : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (homega : 1 ≤ omega)
    (hgamma : 1 ≤ gamma) :
    signedDetectorRate eta omega 1 gamma =
      -Real.logb 2 (1 - eta) - thermalVarianceEntropy omega := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P03

end
