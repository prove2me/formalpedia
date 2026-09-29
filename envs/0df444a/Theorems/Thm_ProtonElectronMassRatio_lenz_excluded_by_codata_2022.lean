-- Prove2me | Theorems.Thm_ProtonElectronMassRatio_lenz_excluded_by_codata_2022
-- name    : ProtonElectronMassRatio.lenz_excluded_by_codata_2022
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T20:19:47.314986+00:00
-- url     : https://prove2.me/theorems/1ed886f0-1469-4631-9961-54566aa38422
-- title:
--   $|\mu_{2022} - 6\pi^5| > 10^6 \cdot u_{2022}$
-- statement:
--   Lenz's expression is excluded by the CODATA 2022 value by more than a million standard uncertainties:
--   $$|1836.152673426 - 6\pi^5| > 10^6 \times 3.2\times10^{-8} = 0.032.$$
--   The actual discrepancy is about $0.03456$, i.e. roughly $1.08\times10^6$ standard uncertainties, so the factor $10^6$ is stated with slack.
-- source:
--   Wikipedia, "Proton-to-electron mass ratio", revision 1371273020, https://en.wikipedia.org/w/index.php?title=Proton-to-electron_mass_ratio&oldid=1371273020 — lead section (CODATA 2022 value 1836.152673426(32)) and the section "A mathematical coincidence" (F. Lenz, Phys. Rev. 82 (1951) 554, value 1836.12 ± 0.05 vs 6π⁵)

import Mathlib
import Definitions.Def_ProtonElectronMassRatio_constants

namespace ProtonElectronMassRatio

theorem lenz_excluded_by_codata_2022 :
    codataUncertainty * 10 ^ 6 < |codataValue - lenzExpression| := by sorry

end ProtonElectronMassRatio
