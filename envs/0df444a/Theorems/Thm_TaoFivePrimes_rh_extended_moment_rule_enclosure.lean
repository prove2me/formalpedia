-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_extended_moment_rule_enclosure
-- name    : TaoFivePrimes.rh_extended_moment_rule_enclosure
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T18:55:24.071054+00:00
-- url     : https://prove2.me/theorems/43796b06-b8d9-45e0-9855-0990133aa898
-- title:
--   Mellin moment enclosure by the rational rule at every order
-- statement:
--   Let $M_j$ be the scaled even Mellin moment of the Riemann-zeta theta kernel, and let $Q_j$ be the rational sixteen-panel rule defined from the published theta-jet data. For every nonnegative integer $j$,
--
--   $$
--   |M_j-Q_j|\le10^{-46}.
--   $$
--
--   The assertion extends the analytic moment enclosure to arbitrary indices. Obtaining useful explicit rounded values from the rational rule requires separate exact computations; this statement by itself does not verify any new zeta zeros.
-- source:
--   Generalization of the 16-panel Mellin and theta-jet argument in sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations by Gabewhigham. The original packed moment certificate covers j<256; the uniform analytic quadrature and jet bounds used here apply to every j.

import Definitions.Def_TaoFivePrimes_RH14To100MomentModel
import Definitions.Def_TaoFivePrimes_RHExtendedMomentRule

theorem TaoFivePrimes.rh_extended_moment_rule_enclosure (j : ℕ) :
    ‖(CertifiedGlobalMoments.moment j:ℂ)-(TaoFivePrimes_RHExtendedMomentRule j:ℂ)‖ ≤ 1/10^46 := by sorry
