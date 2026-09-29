-- Prove2me | Theorems.Thm_SIBrochure_kilogram_from_defining_constants
-- name    : SIBrochure.kilogram_from_defining_constants
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:21:28.025982+00:00
-- url     : https://prove2.me/theorems/452ddee2-e906-45d2-9b09-e19d6172a64c
-- title:
--   The kilogram from $h$, $\Delta\nu_{\mathrm{Cs}}$ and $c$
-- statement:
--   With $h = 6.626\,070\,15\times10^{-34}\ \mathrm{J\,s}$, $c = 299\,792\,458\ \mathrm{m\,s^{-1}}$, $\Delta\nu_{\mathrm{Cs}} = 9\,192\,631\,770\ \mathrm{Hz}$ and $\mathrm J = \mathrm{kg\,m^2\,s^{-2}}$,
--   $$1\ \mathrm{kg} = \frac{h}{6.626\,070\,15\times10^{-34}}\,\mathrm m^{-2}\,\mathrm s \qquad\text{and}\qquad 1\ \mathrm{kg} = \frac{(299\,792\,458)^2}{(6.626\,070\,15\times10^{-34})(9\,192\,631\,770)}\,\frac{h\,\Delta\nu_{\mathrm{Cs}}}{c^2}.$$
--
--   These are the two exact expressions of the kilogram displayed in Section 2.3.1.
-- source:
--   BIPM, The International System of Units (SI), 9th edition (2019), ISBN 978-92-822-2272-0, https://www.bipm.org/en/publications/si-brochure — Section 2.3.1 'The kilogram', p. 131: 1 kg = (h/6.626 070 15 × 10^−34) m^−2 s = (299 792 458)^2/((6.626 070 15 × 10^−34)(9 192 631 770)) hΔνCs/c^2.

import Definitions.Def_SIBrochure_units

namespace SIBrochure

theorem kilogram_from_defining_constants :
    kilogram = (1 / 6.62607015e-34 : ℝ) • (h * metre ^ (-2 : ℤ) * second) ∧
    kilogram = ((299792458 : ℝ) ^ 2 / (6.62607015e-34 * 9192631770)) •
      (h * deltaNuCs / c ^ (2 : ℤ)) := by sorry

end SIBrochure
