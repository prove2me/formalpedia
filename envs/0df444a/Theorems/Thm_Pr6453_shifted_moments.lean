-- Prove2me | Theorems.Thm_Pr6453_shifted_moments
-- name    : Pr6453.shifted_moments
-- status  : Open
-- author  : @gustasmickus
-- created : 2026-11-08T16:45:46.157289+00:00
-- url     : https://prove2.me/theorems/b75e560e-b48f-4513-bc60-916f570d76dc
-- title:
--   PR #6453: the moments at the tested saving $1-t$ and one step out
-- statement:
--   The two rank moments of the PR #6453 word at the tested saving $t = 3287019/10^9$, enclosed.
--
--   The three tail ratios of the strictification, $\alpha$, $\gamma$ and $\delta$, are ratios of these two moments at the exponents $1-t$ and $1-t+\tfrac17$, so bounding them needs the moments there rather than at the claimed saving $1-\kappa$. This node supplies that: the productive moment $\sum_r T_r\,r^{1-t}$ is at least $183876.163374$, the paid moment $\sum_r P_r\,r^{1-t}$ is at most $183876.163305$, and the paid moment one step further out, $\sum_r P_r\,r^{1-t+1/7}$, is at most $242327.543574$.
--
--   The exponents differ from the claimed $1-\kappa$ by only $5\times10^{-9}$ and $1/7$, so the powers are taken in the form $r^{1+c} = r\,e^{c\log r}$ with $|c\log r| \le 0.7$: the same exponential enclosure applies, on the logarithm bounds already proved for the nineteen ranks of the support. The first two enclosures put the ratio at most $0.9999999996$, which is the tight one — the margin above one is $6.9\times10^{-10}$ — and the third puts $\gamma$ at most $0.92408$ against the threshold $31/32$.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, research/p104-third-anchor-clean-mixed-root/pricing.py (alpha, gamma, delta: moments at 1-TESTED and 1-TESTED+1/7) and RESULT.json (complete_cost.strictification).

import Definitions.Def_Pr6453_RankMoments
import Definitions.Def_Pr6453_Strictification

set_option autoImplicit false

namespace Pr6453

theorem shifted_moments :
    (183876.163374 : ℝ) ≤ moment targets (1 - (tested:ℝ)) ∧
      moment paid (1 - (tested:ℝ)) ≤ (183876.163305 : ℝ) ∧
      moment paid (1 - (tested:ℝ) + 1/7) ≤ (242327.543574 : ℝ) := by
  sorry

end Pr6453
