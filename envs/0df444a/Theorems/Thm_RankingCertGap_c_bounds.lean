-- Prove2me | Theorems.Thm_RankingCertGap_c_bounds
-- name    : RankingCertGap.c_bounds
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:49:42.660993+00:00
-- url     : https://prove2.me/theorems/0d0c6b04-096e-43aa-adc0-9e9d3c644707
-- title:
--   Display (181), p.61 — numerical bounds on $c$
-- statement:
--   The defining series for $c=1-\sum_{k\ge1}2^{-(2^k+k-1)}$ gives
--
--   $$
--   \frac{71777}{100000}<c<\frac{359}{500}.
--   $$
--
--   The lower bound places $c$ above $715361/10^6$ and so separates $\gamma(2)$ from $\Gamma_{\mathcal A}(2)$.
--
--   Differences from the source:
--   - encoding: $\sum_{k=1}^\infty2^{-(2^k+k-1)}$ → $\sum_{k\ge0}(1/2)^{2^{k+1}+k}$; reason: index shift; same series
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), App. F.2, eq. (181), p.61

import Mathlib
import Definitions.Def_RankingCertGap_SafetyState

namespace RankingCertGap

/-- **Display (181).** Xu, arXiv:2610.17545 (held file sha256 75896dd9…), App. F.2, p.61: "The defining
series for `c` gives `71777/100000 < c < 359/500`." -/
theorem c_bounds : (71777 : ℝ) / 100000 < cStar ∧ cStar < 359 / 500 := by sorry

end RankingCertGap
