-- Prove2me | Theorems.Thm_SIBrochure_metre_from_defining_constants
-- name    : SIBrochure.metre_from_defining_constants
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:19:52.170275+00:00
-- url     : https://prove2.me/theorems/05b97ff5-e434-438a-a807-c951d2d74374
-- title:
--   The metre from $c$ and $\Delta\nu_{\mathrm{Cs}}$
-- statement:
--   With $c = 299\,792\,458\ \mathrm{m\,s^{-1}}$ and $\Delta\nu_{\mathrm{Cs}} = 9\,192\,631\,770\ \mathrm{Hz}$,
--   $$1\ \mathrm m = \frac{c}{299\,792\,458}\,\mathrm s \qquad\text{and}\qquad 1\ \mathrm m = \frac{9\,192\,631\,770}{299\,792\,458}\,\frac{c}{\Delta\nu_{\mathrm{Cs}}}.$$
--
--   These are the two exact expressions of the metre displayed in Section 2.3.1.
-- source:
--   BIPM, The International System of Units (SI), 9th edition (2019), ISBN 978-92-822-2272-0, https://www.bipm.org/en/publications/si-brochure — Section 2.3.1 'The metre', p. 131: 1 m = (c/299 792 458) s = (9 192 631 770/299 792 458) c/ΔνCs.

import Definitions.Def_SIBrochure_units

namespace SIBrochure

theorem metre_from_defining_constants :
    metre = (1 / 299792458 : ℝ) • (c * second) ∧
    metre = (9192631770 / 299792458 : ℝ) • (c / deltaNuCs) := by sorry

end SIBrochure
