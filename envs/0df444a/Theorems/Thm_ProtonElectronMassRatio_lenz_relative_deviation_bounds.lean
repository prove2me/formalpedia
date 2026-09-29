-- Prove2me | Theorems.Thm_ProtonElectronMassRatio_lenz_relative_deviation_bounds
-- name    : ProtonElectronMassRatio.lenz_relative_deviation_bounds
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T20:20:15.542986+00:00
-- url     : https://prove2.me/theorems/0a1dcc64-5c40-495d-ade6-145056e7920d
-- title:
--   $1.88\times10^{-5} < (\mu_{2022} - 6\pi^5)/\mu_{2022} < 1.89\times10^{-5}$
-- statement:
--   The relative deviation of Lenz's expression from the CODATA 2022 value is pinned to three significant figures:
--   $$1.88\times10^{-5} < \frac{1836.152673426 - 6\pi^5}{1836.152673426} < 1.89\times10^{-5}.$$
--   Its numerical value is about $1.8825\times10^{-5}$. In particular the deviation is positive: $6\pi^5$ is smaller than the measured ratio.
-- source:
--   Wikipedia, "Proton-to-electron mass ratio", revision 1371273020, https://en.wikipedia.org/w/index.php?title=Proton-to-electron_mass_ratio&oldid=1371273020 — lead section (CODATA 2022 value 1836.152673426(32)) and the section "A mathematical coincidence" (F. Lenz, Phys. Rev. 82 (1951) 554, value 1836.12 ± 0.05 vs 6π⁵)

import Mathlib
import Definitions.Def_ProtonElectronMassRatio_constants

namespace ProtonElectronMassRatio

theorem lenz_relative_deviation_bounds :
    0.0000188 < (codataValue - lenzExpression) / codataValue ∧
      (codataValue - lenzExpression) / codataValue < 0.0000189 := by sorry

end ProtonElectronMassRatio
