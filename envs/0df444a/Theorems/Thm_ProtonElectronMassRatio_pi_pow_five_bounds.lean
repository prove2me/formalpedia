-- Prove2me | Theorems.Thm_ProtonElectronMassRatio_pi_pow_five_bounds
-- name    : ProtonElectronMassRatio.pi_pow_five_bounds
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T19:53:02.227906+00:00
-- url     : https://prove2.me/theorems/a8c0f16c-9167-4b75-84fb-6093eb40e866
-- title:
--   $306.019684 < \pi^5 < 306.019685$
-- statement:
--   The fifth power of $\pi$ is enclosed between two explicit rationals:
--   $$306.019684 < \pi^5 < 306.019685.$$
--   The enclosure has relative width about $3\times10^{-9}$, so it needs bounds on $\pi$ itself of relative precision about $6\times10^{-10}$; Mathlib's 20-digit bounds `Real.pi_gt_d20` and `Real.pi_lt_d20` are more than sufficient, while the commonly used six-digit bounds are not. Numerically $\pi^5 = 306.0196847852\ldots$
-- source:
--   Wikipedia, "Proton-to-electron mass ratio", revision 1371273020, https://en.wikipedia.org/w/index.php?title=Proton-to-electron_mass_ratio&oldid=1371273020 — lead section (CODATA 2022 value 1836.152673426(32)) and the section "A mathematical coincidence" (F. Lenz, Phys. Rev. 82 (1951) 554, value 1836.12 ± 0.05 vs 6π⁵)

import Mathlib
import Definitions.Def_ProtonElectronMassRatio_constants

namespace ProtonElectronMassRatio

theorem pi_pow_five_bounds :
    306.019684 < Real.pi ^ 5 ∧ Real.pi ^ 5 < 306.019685 := by sorry

end ProtonElectronMassRatio
