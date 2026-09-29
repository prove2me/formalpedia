-- Prove2me | Theorems.Thm_SIBrochure_kelvin_from_defining_constants
-- name    : SIBrochure.kelvin_from_defining_constants
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:34:31.422626+00:00
-- url     : https://prove2.me/theorems/fd1e19a9-28e4-46ad-9e1e-b3171cebcf92
-- title:
--   The kelvin from $k$, $h$ and $\Delta\nu_{\mathrm{Cs}}$
-- statement:
--   With $k = 1.380\,649\times10^{-23}\ \mathrm{J\,K^{-1}}$, $h = 6.626\,070\,15\times10^{-34}\ \mathrm{J\,s}$, $\Delta\nu_{\mathrm{Cs}} = 9\,192\,631\,770\ \mathrm{Hz}$ and $\mathrm J = \mathrm{kg\,m^2\,s^{-2}}$,
--   $$1\ \mathrm K = \frac{1.380\,649\times10^{-23}}{k}\,\mathrm{kg\,m^2\,s^{-2}} \qquad\text{and}\qquad 1\ \mathrm K = \frac{1.380\,649\times10^{-23}}{(6.626\,070\,15\times10^{-34})(9\,192\,631\,770)}\,\frac{\Delta\nu_{\mathrm{Cs}}\,h}{k}.$$
--
--   These are the two exact expressions of the kelvin displayed in Section 2.3.1.
-- source:
--   BIPM, The International System of Units (SI), 9th edition (2019), ISBN 978-92-822-2272-0, https://www.bipm.org/en/publications/si-brochure — Section 2.3.1 'The kelvin', p. 133: 1 K = (1.380 649/k) × 10^−23 kg m^2 s^−2 = (1.380 649 × 10^−23)/((6.626 070 15 × 10^−34)(9 192 631 770)) ΔνCs h/k.

import Definitions.Def_SIBrochure_units

namespace SIBrochure

theorem kelvin_from_defining_constants :
    kelvin = (1.380649e-23 : ℝ) •
      (k⁻¹ * kilogram * metre ^ (2 : ℤ) * second ^ (-2 : ℤ)) ∧
    kelvin = (1.380649e-23 / (6.62607015e-34 * 9192631770) : ℝ) •
      (deltaNuCs * h / k) := by sorry

end SIBrochure
