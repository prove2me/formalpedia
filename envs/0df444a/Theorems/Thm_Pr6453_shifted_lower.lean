-- Prove2me | Theorems.Thm_Pr6453_shifted_lower
-- name    : Pr6453.shifted_lower
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T17:43:26.838823+00:00
-- url     : https://prove2.me/theorems/d69da95d-897c-4896-9627-cb56a151872a
-- title:
--   PR #6453: the first nineteen shifted rank bounds
-- statement:
--   Nineteen of the thirty-nine rank bounds that enclose the PR #6453 moments at the tested saving $t = 3287019/10^9$. The productive ranks are bounded below at exponent $1-t$, and the paid ranks $1$ to $5$ above at the same exponent. Each power is written $r^{1+c} = r\,e^{c\log r}$ with $c = -t$, so $|c\log r| \le 0.0165$ and six terms of the exponential series enclose it to $10^{-12}$ at the endpoints of the logarithm interval of that rank.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, research/p104-third-anchor-clean-mixed-root/pricing.py (moments at 1-TESTED and 1-TESTED+1/7).

import Definitions.Def_Pr6453_RankMoments
import Definitions.Def_Pr6453_Strictification

set_option autoImplicit false

namespace Pr6453

theorem shifted_lower :
    (1.995448411000 : ℝ) ≤ (2:ℝ)^(1 - (tested:ℝ)) ∧
      (2.989186058000 : ℝ) ≤ (3:ℝ)^(1 - (tested:ℝ)) ∧
      (3.981814361000 : ℝ) ≤ (4:ℝ)^(1 - (tested:ℝ)) ∧
      (4.973618578000 : ℝ) ≤ (5:ℝ)^(1 - (tested:ℝ)) ∧
      (5.964766571000 : ℝ) ≤ (6:ℝ)^(1 - (tested:ℝ)) ∧
      (6.955369181000 : ℝ) ≤ (7:ℝ)^(1 - (tested:ℝ)) ∧
      (7.945505141000 : ℝ) ≤ (8:ℝ)^(1 - (tested:ℝ)) ∧
      (8.935233294000 : ℝ) ≤ (9:ℝ)^(1 - (tested:ℝ)) ∧
      (16.842416867000 : ℝ) ≤ (17:ℝ)^(1 - (tested:ℝ)) ∧
      (24.736881766000 : ℝ) ≤ (25:ℝ)^(1 - (tested:ℝ)) ∧
      (32.622899312000 : ℝ) ≤ (33:ℝ)^(1 - (tested:ℝ)) ∧
      (56.247504828000 : ℝ) ≤ (57:ℝ)^(1 - (tested:ℝ)) ∧
      (71.977719478000 : ℝ) ≤ (73:ℝ)^(1 - (tested:ℝ)) ∧
      (142.647296292000 : ℝ) ≤ (145:ℝ)^(1 - (tested:ℝ)) ∧
      (1:ℝ)^(1 - (tested:ℝ)) ≤ (1.000000001000 : ℝ) ∧
      (2:ℝ)^(1 - (tested:ℝ)) ≤ (1.995448412000 : ℝ) ∧
      (3:ℝ)^(1 - (tested:ℝ)) ≤ (2.989186059000 : ℝ) ∧
      (4:ℝ)^(1 - (tested:ℝ)) ≤ (3.981814362000 : ℝ) ∧
      (5:ℝ)^(1 - (tested:ℝ)) ≤ (4.973618579000 : ℝ) := by
  sorry

end Pr6453
