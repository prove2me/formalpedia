-- Prove2me | Theorems.Thm_SIBrochure_every_unit_from_defining_constants
-- name    : SIBrochure.every_unit_from_defining_constants
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T16:08:30.384976+00:00
-- url     : https://prove2.me/theorems/eea83803-ad4f-490b-8b74-417211623c79
-- title:
--   Every SI unit is a multiple of a product of powers of the seven defining constants
-- statement:
--   Let $\Delta\nu_{\mathrm{Cs}}, c, h, e, k, N_A, K_{\mathrm{cd}}$ be the seven defining constants of the SI, regarded as quantity values (a real numerical value times a monomial in the base units). For every choice of integer exponents $u_1,\dots,u_7$ there exist a real number $a$ and integers $n_1,\dots,n_7$ such that
--
--   $$\mathrm{s}^{u_1}\,\mathrm{m}^{u_2}\,\mathrm{kg}^{u_3}\,\mathrm{A}^{u_4}\,\mathrm{K}^{u_5}\,\mathrm{mol}^{u_6}\,\mathrm{cd}^{u_7} \;=\; a\cdot \Delta\nu_{\mathrm{Cs}}^{\,n_1}\, c^{\,n_2}\, h^{\,n_3}\, e^{\,n_4}\, k^{\,n_5}\, N_A^{\,n_6}\, K_{\mathrm{cd}}^{\,n_7}.$$
--
--   This is the Brochure's statement that any unit of the SI can be written through products and quotients of the defining constants; it is the goal of the mission.
--
--   **Formalization Note** The left side is the unit monomial with numerical value $1$; equality means equal numerical values and equal exponents of all seven base units. The product runs over the seven defining constants.
-- source:
--   BIPM, The International System of Units (SI), 9th edition (2019), ISBN 978-92-822-2272-0, https://www.bipm.org/en/publications/si-brochure — Section 2.2 'Definition of the SI', p. 127: 'The seven constants are chosen in such a way that any unit of the SI can be written either through a defining constant itself or through products or quotients of defining constants.'

import Definitions.Def_SIBrochure_units

namespace SIBrochure

theorem every_unit_from_defining_constants (u : BaseUnit → ℤ) :
    ∃ (a : ℝ) (n : DefiningConstant → ℤ),
      unitOf u = a • ∏ i : DefiningConstant, i.value ^ (n i) := by sorry

end SIBrochure
