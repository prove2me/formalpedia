-- Prove2me | Theorems.Thm_SIBrochure_second_from_defining_constants
-- name    : SIBrochure.second_from_defining_constants
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:09:29.579853+00:00
-- url     : https://prove2.me/theorems/88d359e7-60c8-476c-a3af-6888f503b43a
-- title:
--   The second from $\Delta\nu_{\mathrm{Cs}}$
-- statement:
--   With $\Delta\nu_{\mathrm{Cs}} = 9\,192\,631\,770\ \mathrm{Hz}$ and $\mathrm{Hz} = \mathrm s^{-1}$,
--   $$1\ \mathrm{Hz} = \frac{\Delta\nu_{\mathrm{Cs}}}{9\,192\,631\,770}\qquad\text{and}\qquad 1\ \mathrm s = \frac{9\,192\,631\,770}{\Delta\nu_{\mathrm{Cs}}}.$$
--
--   This expresses the second through the caesium hyperfine frequency alone, as in the definition of the second in Section 2.3.1.
-- source:
--   BIPM, The International System of Units (SI), 9th edition (2019), ISBN 978-92-822-2272-0, https://www.bipm.org/en/publications/si-brochure — Section 2.3.1 'The second', p. 130: 1 Hz = ΔνCs/9 192 631 770, 1 s = 9 192 631 770/ΔνCs.

import Definitions.Def_SIBrochure_units

namespace SIBrochure

theorem second_from_defining_constants :
    hertz = (1 / 9192631770 : ℝ) • deltaNuCs ∧
    second = (9192631770 : ℝ) • deltaNuCs⁻¹ := by sorry

end SIBrochure
