-- Prove2me | Theorems.Thm_SIBrochure_ampere_from_defining_constants
-- name    : SIBrochure.ampere_from_defining_constants
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:31:27.804291+00:00
-- url     : https://prove2.me/theorems/ab7bdfec-641b-4cae-a9c0-1948b04ae50b
-- title:
--   The ampere from $e$ and $\Delta\nu_{\mathrm{Cs}}$
-- statement:
--   With $e = 1.602\,176\,634\times10^{-19}\ \mathrm C$, $\mathrm C = \mathrm{A\,s}$ and $\Delta\nu_{\mathrm{Cs}} = 9\,192\,631\,770\ \mathrm{Hz}$,
--   $$1\ \mathrm A = \frac{e}{1.602\,176\,634\times10^{-19}}\,\mathrm s^{-1} \qquad\text{and}\qquad 1\ \mathrm A = \frac{\Delta\nu_{\mathrm{Cs}}\,e}{(9\,192\,631\,770)(1.602\,176\,634\times10^{-19})}.$$
--
--   These are the two exact expressions of the ampere displayed in Section 2.3.1.
-- source:
--   BIPM, The International System of Units (SI), 9th edition (2019), ISBN 978-92-822-2272-0, https://www.bipm.org/en/publications/si-brochure — Section 2.3.1 'The ampere', p. 132: 1 A = (e/1.602 176 634 × 10^−19) s^−1 = ΔνCs e/((9 192 631 770)(1.602 176 634 × 10^−19)).

import Definitions.Def_SIBrochure_units

namespace SIBrochure

theorem ampere_from_defining_constants :
    ampere = (1 / 1.602176634e-19 : ℝ) • (e * second⁻¹) ∧
    ampere = (1 / (9192631770 * 1.602176634e-19) : ℝ) • (deltaNuCs * e) := by sorry

end SIBrochure
