-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P04_pureLossReach
-- name    : QAlgorithms.Papers.Independent.Bridge50.P04.pureLossReach
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:55:58.75166+00:00
-- url     : https://prove2.me/theorems/2aa217f9-a00f-416b-a4e6-1fb491b67841
-- title:
--   Pure-loss positivity and vanishing at zero transmission
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
--   The pure-loss expression satisfies
--
--   $$L(\tau)>0\quad(0<\tau<1),\qquad \lim_{\substack{\tau\to0\\0<\tau<1}}L(\tau)=0.$$
--
--   This expresses the absence of a finite pure-loss cutoff and the vanishing limit at infinite fibre distance. It supplies no uniform positive lower bound and does not evaluate the formula at $\tau=0$ or $\tau=1$.
-- source:
--   Quantum cryptography with an ideal local relay, arXiv:1509.01113v1, PDF p. 2, §3, sentence following Eq. (3)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P04

namespace QAlgorithms.Papers.Independent.Bridge50.P04

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

/-- arXiv:1509.01113v1, PDF p.2, sentence after Eq. (3): the pure-loss
expression is positive at every finite lossy link and tends to zero as the
transmissivity tends to zero through its physical open interval.
No assertion evaluates the totalized formula at either endpoint. -/
theorem pureLossReach :
    (∀ tau : ℝ, 0 < tau → tau < 1 → 0 < pureLossRate tau) ∧
      Filter.Tendsto pureLossRate (nhdsWithin (0 : ℝ) (Set.Ioo 0 1)) (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P04
