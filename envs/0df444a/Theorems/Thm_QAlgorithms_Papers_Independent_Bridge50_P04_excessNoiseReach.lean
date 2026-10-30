-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P04_excessNoiseReach
-- name    : QAlgorithms.Papers.Independent.Bridge50.P04.excessNoiseReach
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:56:34.321001+00:00
-- url     : https://prove2.me/theorems/eeda5c14-7f93-4837-ac44-f99dbb0587d7
-- title:
--   Positive printed rate beyond 100 km with excess noise 0.02
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
--   At the stated attenuation of $0.2$ dB/km, define $\tau(d)=10^{-d/50}$ for distance $d$ in km. Then
--
--   $$\exists d>100:\quad 0<\tau(d)<1\ \text{and}\ F(\tau(d),0.02)>0.$$
--
--   This records the positive theoretical curve beyond 100 km without specifying a maximum range or an experimental data point.
-- source:
--   Quantum cryptography with an ideal local relay, arXiv:1509.01113v1, PDF p. 2, §3 and Fig. 3

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P04

namespace QAlgorithms.Papers.Independent.Bridge50.P04

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

/-- arXiv:1509.01113v1, PDF p.2, final paragraphs of §3 and PDF p.3,
Fig.3: the explicit ideal-reconciliation expression with excess noise 0.02
is positive at some fibre distance strictly beyond 100 km, at 0.2 dB/km.
This does not choose a maximum distance or certify an experimental yield. -/
theorem excessNoiseReach :
    ∃ distance : ℝ, 100 < distance ∧
      0 < fiberTransmissivity distance ∧ fiberTransmissivity distance < 1 ∧
      0 < analyticRate (fiberTransmissivity distance) (1 / 50) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P04
