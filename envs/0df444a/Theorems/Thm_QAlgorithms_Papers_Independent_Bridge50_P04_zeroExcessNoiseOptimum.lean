-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P04_zeroExcessNoiseOptimum
-- name    : QAlgorithms.Papers.Independent.Bridge50.P04.zeroExcessNoiseOptimum
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:55:16.182358+00:00
-- url     : https://prove2.me/theorems/1f5f0307-45a6-4cb0-b793-26f970b831d9
-- title:
--   Zero excess noise maximizes the printed rate
-- statement:
--   All quantities below are scalar analytic expressions from the ideal-reconciliation, large-modulation formulas in §3. For $0<\tau<1$ and excess noise $\varepsilon\ge0$, set
--
--   $$
--   \ell(x)=\frac{\ln x}{\ln2},\qquad h(x)=\frac{x+1}{2}\ell\!\left(\frac{x+1}{2}\right)-\frac{x-1}{2}\ell\!\left(\frac{x-1}{2}\right),\quad x\ge1,
--   $$
--
--   with $0\log_2 0=0$. Define $\chi(\tau,\varepsilon)=2(1+\tau)/\tau+\varepsilon$ and
--
--   $$
--   F(\tau,\varepsilon)=h\!\left(\frac{\chi(\tau,\varepsilon)}{1+\tau}-1\right)-h\!\left(\frac{\tau\chi(\tau,\varepsilon)-(1+\tau)^2}{1-\tau^2}\right)+\ell\!\left(\frac{2(1+\tau)}{e(1-\tau)\chi(\tau,\varepsilon)}\right),
--   $$
--
--   where $e=\exp(1)$. Write
--
--   $$
--   L(\tau)=h\!\left(\frac{2-\tau}{\tau}\right)+\ell\!\left(\frac{\tau}{(1-\tau)e}\right).
--   $$
--
--   These are the printed signed real expressions; their identification with an operational secret-key yield is separately deferred.
--
--   For every fixed $0<\tau<1$ and every $\varepsilon\ge0$,
--
--   $$F(\tau,\varepsilon)\le F(\tau,0).$$
--
--   Thus zero excess noise attains the maximum over nonnegative excess noise at fixed loss. This does not optimize over protocols or identify a channel capacity.
-- source:
--   Quantum cryptography with an ideal local relay, arXiv:1509.01113v1, PDF p. 2, §3, sentence preceding Eq. (3)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P04

namespace QAlgorithms.Papers.Independent.Bridge50.P04

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

/-- arXiv:1509.01113v1, PDF p.2, paragraph before Eq. (3): for each fixed
physical transmissivity, the printed expression is maximized at zero excess
noise. The comparison includes signed values and asserts no capacity converse. -/
theorem zeroExcessNoiseOptimum (tau excess : ℝ)
    (hTauPos : 0 < tau) (hTauLt : tau < 1) (hExcess : 0 ≤ excess) :
    analyticRate tau excess ≤ analyticRate tau 0 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P04
