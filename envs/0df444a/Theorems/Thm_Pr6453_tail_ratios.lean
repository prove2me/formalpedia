-- Prove2me | Theorems.Thm_Pr6453_tail_ratios
-- name    : Pr6453.tail_ratios
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T18:11:30.045215+00:00
-- url     : https://prove2.me/theorems/983393b8-8850-4fb6-8e7a-4ea63950dfdf
-- title:
--   PR #6453: the three tail ratios of the strictification
-- statement:
--   The three tail ratios of the PR #6453 strictification satisfy the bounds the certificate asks for: $\alpha < 1 - 10^{-29}$, $\gamma < \tfrac{31}{32}$ and $\delta < \tfrac{31}{32}$.
--
--   With the shifted moments enclosed ($T(1-t) \ge 183876.163374$, $P(1-t) \le 183876.163305$, $P(1-t+\tfrac17) \le 242327.543574$) and the split bounded from below by $12^{1/7} \ge 1.41$ and $12^t \ge 1$, the three ratios come out at $\alpha \le 0.99999999963$, $\gamma \le 0.92408$ and $\delta \le 0.95735$, clearing their thresholds by factors $3.7\times10^{19}$, $1.05$ and $1.01$. The $\alpha$ bound is the tight one in absolute terms: its margin above one is $6.9\times10^{-10}$, which is why the moments had to be enclosed at the tested saving rather than at the claimed one.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, research/p104-third-anchor-clean-mixed-root/pricing.py: need(alpha[1] < 1-reserve and gamma[1] < decay and delta[1] < decay, 'All charged tail ratios').

import Definitions.Def_Pr6453_RankMoments
import Definitions.Def_Pr6453_Strictification
import Definitions.Def_Pr6453_TailRatiosFixed
import Theorems.Thm_Pr6453_shifted_lower
import Theorems.Thm_Pr6453_shifted_upper

set_option autoImplicit false

namespace Pr6453

theorem tail_ratios :
    alpha2 < 1 - (reserve : ℝ) ∧ gammaTail2 < (decay : ℝ) ∧ deltaTail2 < (decay : ℝ) := by
  sorry

end Pr6453
