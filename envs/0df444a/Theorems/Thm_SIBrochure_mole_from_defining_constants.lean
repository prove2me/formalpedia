-- Prove2me | Theorems.Thm_SIBrochure_mole_from_defining_constants
-- name    : SIBrochure.mole_from_defining_constants
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:38:22.532427+00:00
-- url     : https://prove2.me/theorems/454bd184-d11e-4aaf-a069-83ab0a38c3e5
-- title:
--   The mole from $N_A$
-- statement:
--   With $N_A = 6.022\,140\,76\times10^{23}\ \mathrm{mol^{-1}}$,
--   $$1\ \mathrm{mol} = \frac{6.022\,140\,76\times10^{23}}{N_A}.$$
--
--   This is the exact expression of the mole displayed in Section 2.3.1.
-- source:
--   BIPM, The International System of Units (SI), 9th edition (2019), ISBN 978-92-822-2272-0, https://www.bipm.org/en/publications/si-brochure — Section 2.3.1 'The mole', p. 134: 1 mol = 6.022 140 76 × 10^23/NA.

import Definitions.Def_SIBrochure_units

namespace SIBrochure

theorem mole_from_defining_constants :
    mole = (6.02214076e23 : ℝ) • NA⁻¹ := by sorry

end SIBrochure
