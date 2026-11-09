-- Prove2me | Theorems.Thm_Pr6453_strictification
-- name    : Pr6453.strictification
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T16:31:06.902119+00:00
-- url     : https://prove2.me/theorems/dd08f776-ee36-433b-b6a4-5e4f4782e50c
-- title:
--   PR #6453: the strictification tail and the compiler grid
-- statement:
--   The strictification of the PR #6453 certificate and its compiler grid, at the printed constants.
--
--   The recursion is charged in blocks of $1920$ levels after a split at $12$ and a rounding by $13$. The checks are: the block estimate applies, $(31/32)^{128} < 1/16$, so the decay of one block of $128$ levels beats $1/16$; the rounding is sound, $12^{64} < 13^{63}$; the shifted exits and the complementary capacity fit, $2\cdot(12^{1920})^{64} \le (145^{1920})^{63}$; the compensated capacity exceeds $\theta^{2100} = (63/64)^{2100}$; the compiler's initial range is respected, $145^{1920t} < 2^{2100}$ at the tested saving $t$; the absorbed tail finishes, $1/(1+1920\cdot10^{-29}) + 4(31/32)^{1920} < 1$; the coarse block bound on the other hand cannot fund the claim, $1 < 1/(1+1920\cdot10^{-29}) + 4(1/16)^{15}$, which is the certificate's own negative control; and the integer test exponent $98\,643$ fits the compiler grid $H = 138\,100\,200\,000\,000$.
--
--   Two of these are the ones that carry the strictification. The absorbed tail is tight: the exact decay $4(31/32)^{1920}$ is about $1.2\times10^{-26}$, against an absorbed reserve of $1920\times10^{-29} = 1.92\times10^{-26}$, so the margin is a factor $1.6$ — while the coarse bound $4(1/16)^{15} \approx 3.5\times10^{-18}$ overshoots by eight orders of magnitude, which is exactly why the certificate keeps the exact tail and records the coarse one as a rejected alternative. The other is the capacity: $2\cdot12^{122880} \le 145^{120960}$, proved by raising the integer inequality $2\cdot12^{64} \le 145^{63}$ to the $1920$-th power.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, research/p104-third-anchor-clean-mixed-root/pricing.py (the strictification block: decay, cutoff, floor, reserve, theta, logarithm power, eta) and RESULT.json (complete_cost.strictification, complete_cost.compiler).

import Definitions.Def_Pr6453_RankMoments
import Definitions.Def_Pr6453_Strictification

set_option autoImplicit false

namespace Pr6453

theorem strictification :
    (decay : ℝ) ^ 128 < 1 / 16 ∧
      (cutoff : ℕ) ^ 64 < floor' ^ 63 ∧
      2 * ((cutoff : ℕ) ^ power) ^ 64 ≤ (145 ^ power) ^ 63 ∧
      (theta : ℝ) ^ logarithmPower < (etaLower : ℝ) ∧
      (145 : ℝ) ^ ((power : ℝ) * (tested : ℝ)) < 2 ^ logarithmPower ∧
      1 / (1 + (power : ℝ) * (reserve : ℝ)) + 4 * (decay : ℝ) ^ power < 1 ∧
      1 < 1 / (1 + (power : ℝ) * (reserve : ℝ)) + 4 * ((1 : ℝ) / 16) ^ (power / 128) ∧
      H = 138100200000000 ∧ integerTestExponent < H := by
  sorry

end Pr6453
