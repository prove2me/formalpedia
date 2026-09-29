-- Prove2me | Theorems.Thm_ProtonElectronMassRatio_lenz_consistent_with_1951_measurement
-- name    : ProtonElectronMassRatio.lenz_consistent_with_1951_measurement
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T20:19:27.00979+00:00
-- url     : https://prove2.me/theorems/e4f7cef2-5913-44c0-82b9-608b38dc06fe
-- title:
--   $|6\pi^5 - 1836.12| < 0.05$
-- statement:
--   Lenz's expression lies strictly inside the error bar of the 1951 experimental value:
--   $$|6\pi^5 - 1836.12| < 0.05.$$
--   This is the half of the historical statement that explains why the coincidence was reported: at 1951 precision the expression and the measurement are indistinguishable. Numerically the discrepancy is about $1.9\times10^{-3}$, well inside the quoted $0.05$.
-- source:
--   Wikipedia, "Proton-to-electron mass ratio", revision 1371273020, https://en.wikipedia.org/w/index.php?title=Proton-to-electron_mass_ratio&oldid=1371273020 — lead section (CODATA 2022 value 1836.152673426(32)) and the section "A mathematical coincidence" (F. Lenz, Phys. Rev. 82 (1951) 554, value 1836.12 ± 0.05 vs 6π⁵)

import Mathlib
import Definitions.Def_ProtonElectronMassRatio_constants

namespace ProtonElectronMassRatio

theorem lenz_consistent_with_1951_measurement :
    |lenzExpression - lenz1951Measurement| < lenz1951Uncertainty := by sorry

end ProtonElectronMassRatio
