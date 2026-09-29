-- Prove2me | Theorems.Thm_SIBrochure_candela_from_defining_constants
-- name    : SIBrochure.candela_from_defining_constants
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:56:54.334032+00:00
-- url     : https://prove2.me/theorems/abe5563b-bf6e-4c68-a6aa-5223d20c97d5
-- title:
--   The candela from $K_{\mathrm{cd}}$, $h$ and $\Delta\nu_{\mathrm{Cs}}$
-- statement:
--   With $K_{\mathrm{cd}} = 683\ \mathrm{lm\,W^{-1}}$, $h = 6.626\,070\,15\times10^{-34}\ \mathrm{J\,s}$, $\Delta\nu_{\mathrm{Cs}} = 9\,192\,631\,770\ \mathrm{Hz}$, $\mathrm{lm} = \mathrm{cd\,sr}$, $\mathrm W = \mathrm{kg\,m^2\,s^{-3}}$ and $\mathrm{sr} = \mathrm{m^2\,m^{-2}}$,
--   $$1\ \mathrm{cd} = \frac{K_{\mathrm{cd}}}{683}\,\mathrm{kg\,m^2\,s^{-3}\,sr^{-1}} \qquad\text{and}\qquad 1\ \mathrm{cd} = \frac{(\Delta\nu_{\mathrm{Cs}})^2\,h\,K_{\mathrm{cd}}}{(6.626\,070\,15\times10^{-34})(9\,192\,631\,770)^2\,683}.$$
--
--   These are the two exact expressions of the candela displayed in Section 2.3.1.
--
--   **Formalization Note** The steradian is the unit of dimension one, as in Table 4 of the Brochure.
-- source:
--   BIPM, The International System of Units (SI), 9th edition (2019), ISBN 978-92-822-2272-0, https://www.bipm.org/en/publications/si-brochure — Section 2.3.1 'The candela', p. 135: 1 cd = (Kcd/683) kg m^2 s^−3 sr^−1 = (ΔνCs)^2 h Kcd/((6.626 070 15 × 10^−34)(9 192 631 770)^2 683).

import Definitions.Def_SIBrochure_units

namespace SIBrochure

theorem candela_from_defining_constants :
    candela = (1 / 683 : ℝ) •
      (Kcd * kilogram * metre ^ (2 : ℤ) * second ^ (-3 : ℤ) * steradian⁻¹) ∧
    candela = (1 / (6.62607015e-34 * (9192631770 : ℝ) ^ 2 * 683)) •
      (deltaNuCs ^ (2 : ℤ) * h * Kcd) := by sorry

end SIBrochure
