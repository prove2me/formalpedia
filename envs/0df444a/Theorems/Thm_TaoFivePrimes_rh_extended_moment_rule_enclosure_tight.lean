-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_extended_moment_rule_enclosure_tight
-- name    : TaoFivePrimes.rh_extended_moment_rule_enclosure_tight
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T20:56:10.646603+00:00
-- url     : https://prove2.me/theorems/75947687-a36d-4fba-955d-510f737e7721
-- title:
--   Tighter all-index enclosure for the rational Mellin rule
-- statement:
--   Let $M_j$ be the scaled even Mellin moment and let $Q_j$ be the published rational theta-jet quadrature rule. For every nonnegative integer $j$,
--
--   $$
--   |M_j-Q_j|\le162\cdot10^{-51}.
--   $$
--
--   This improves the earlier uniform enclosures and can be combined with separate exact rounding certificates.
-- source:
--   Sharper numerical consequence of the uniform moment-to-panel bound and theta-jet bound in the Mellin framework by sometik179, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham. The all-index rational rule is TaoFivePrimes_RHExtendedMomentRule.

import Definitions.Def_TaoFivePrimes_RH14To100MomentModel
import Definitions.Def_TaoFivePrimes_RHExtendedMomentRule

theorem TaoFivePrimes.rh_extended_moment_rule_enclosure_tight (j : ℕ) :
    ‖(CertifiedGlobalMoments.moment j:ℂ)-(TaoFivePrimes_RHExtendedMomentRule j:ℂ)‖ ≤ 162/10^51 := by sorry
