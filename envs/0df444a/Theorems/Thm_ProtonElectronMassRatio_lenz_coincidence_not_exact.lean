-- Prove2me | Theorems.Thm_ProtonElectronMassRatio_lenz_coincidence_not_exact
-- name    : ProtonElectronMassRatio.lenz_coincidence_not_exact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T20:23:15.36357+00:00
-- url     : https://prove2.me/theorems/147b1c2c-117a-4d1b-940d-58529307e05c
-- title:
--   The Lenz coincidence is not exact: $6\pi^5 \ne \mu$
-- statement:
--   Let $m_p, m_e$ be reals whose ratio is the CODATA 2022 value, $m_p/m_e = 1836.152673426$. Then Lenz's expression $6\pi^5$ is not that ratio; it is separated from it by more than $10^6$ standard uncertainties,
--   $$|m_p/m_e - 6\pi^5| > 10^6 \times 3.2\times10^{-8},$$
--   its relative deviation satisfies
--   $$1.88\times10^{-5} < \frac{m_p/m_e - 6\pi^5}{m_p/m_e} < 1.89\times10^{-5},$$
--   and nevertheless $6\pi^5$ lies strictly inside the 1951 experimental error bar, $|6\pi^5 - 1836.12| < 0.05$. Together these say exactly that Lenz's 1951 observation is a numerical coincidence: consistent with the data he had, refuted by the data available now.
-- source:
--   Wikipedia, "Proton-to-electron mass ratio", revision 1371273020, https://en.wikipedia.org/w/index.php?title=Proton-to-electron_mass_ratio&oldid=1371273020 — lead section (CODATA 2022 value 1836.152673426(32)) and the section "A mathematical coincidence" (F. Lenz, Phys. Rev. 82 (1951) 554, value 1836.12 ± 0.05 vs 6π⁵)

import Mathlib
import Definitions.Def_ProtonElectronMassRatio_constants

namespace ProtonElectronMassRatio

theorem lenz_coincidence_not_exact (mproton melectron : ℝ)
    (h : mproton / melectron = codataValue) :
    mproton / melectron ≠ lenzExpression ∧
      codataUncertainty * 10 ^ 6 < |mproton / melectron - lenzExpression| ∧
      0.0000188 < (mproton / melectron - lenzExpression) / (mproton / melectron) ∧
      (mproton / melectron - lenzExpression) / (mproton / melectron) < 0.0000189 ∧
      |lenzExpression - lenz1951Measurement| < lenz1951Uncertainty := by sorry

end ProtonElectronMassRatio
