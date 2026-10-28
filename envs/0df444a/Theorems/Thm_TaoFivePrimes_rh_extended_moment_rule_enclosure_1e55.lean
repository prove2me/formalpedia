-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_extended_moment_rule_enclosure_1e55
-- name    : TaoFivePrimes.rh_extended_moment_rule_enclosure_1e55
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:04:20.806416+00:00
-- url     : https://prove2.me/theorems/21c4560d-33ef-4279-a6d6-8f24d8d3152b
-- title:
--   Improved all-index enclosure for the rational Mellin rule
-- statement:
--   Let $M_j$ be the scaled even Mellin moment and $Q_j$ the published rational theta-jet quadrature rule. For every nonnegative integer $j$,
--
--   $$
--   |M_j-Q_j|\le161\cdot10^{-57}.
--   $$
--
--   This uniform enclosure can be combined with separate exact rounding certificates.
-- source:
--   The theta-jet and Mellin framework is due to sometik179, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham. The wider Cauchy-circle estimate is a separate dependency.

import Definitions.Def_TaoFivePrimes_RH14To100MomentModel
import Definitions.Def_TaoFivePrimes_RHExtendedMomentRule

theorem TaoFivePrimes.rh_extended_moment_rule_enclosure_1e55 (j : ℕ) :
    ‖(CertifiedGlobalMoments.moment j:ℂ)-(TaoFivePrimes_RHExtendedMomentRule j:ℂ)‖ ≤ 161/10^57 := by sorry
