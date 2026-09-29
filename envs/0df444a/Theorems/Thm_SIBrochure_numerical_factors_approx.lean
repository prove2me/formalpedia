-- Prove2me | Theorems.Thm_SIBrochure_numerical_factors_approx
-- name    : SIBrochure.numerical_factors_approx
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:58:39.459192+00:00
-- url     : https://prove2.me/theorems/a9f7e8b5-47e8-47e7-b0eb-e3390921f2b2
-- title:
--   Rounded values of the numerical factors in Section 2.3.1
-- statement:
--   The five numerical factors appearing in the exact expressions of the metre, kilogram, ampere, kelvin and candela agree with the decimal values quoted in the Brochure to within half a unit in the last quoted digit:
--
--   1. $\left|\dfrac{9\,192\,631\,770}{299\,792\,458} - 30.663\,319\right| \le 5\times10^{-7}$;
--   2. $\left|\dfrac{(299\,792\,458)^2}{(6.626\,070\,15\times10^{-34})(9\,192\,631\,770)} - 1.475\,5214\times10^{40}\right| \le 5\times10^{32}$;
--   3. $\left|\dfrac{1}{(9\,192\,631\,770)(1.602\,176\,634\times10^{-19})} - 6.789\,687\times10^{8}\right| \le 50$;
--   4. $\left|\dfrac{1.380\,649\times10^{-23}}{(6.626\,070\,15\times10^{-34})(9\,192\,631\,770)} - 2.266\,6653\right| \le 5\times10^{-8}$;
--   5. $\left|\dfrac{1}{(6.626\,070\,15\times10^{-34})(9\,192\,631\,770)^2\,683} - 2.614\,830\times10^{10}\right| \le 5000$.
--
--   This certifies that the rounded values printed in Section 2.3.1 are correctly rounded.
-- source:
--   BIPM, The International System of Units (SI), 9th edition (2019), ISBN 978-92-822-2272-0, https://www.bipm.org/en/publications/si-brochure — Section 2.3.1, pp. 131–135: the approximations ≈ 30.663 319, ≈ 1.475 5214 × 10^40, ≈ 6.789 687 × 10^8, ≈ 2.266 6653, ≈ 2.614 830 × 10^10.

import Definitions.Def_SIBrochure_units

namespace SIBrochure

theorem numerical_factors_approx :
    |(9192631770 / 299792458 : ℝ) - 30.663319| ≤ 5e-7 ∧
    |(299792458 : ℝ) ^ 2 / (6.62607015e-34 * 9192631770) - 1.4755214e40| ≤ 5e32 ∧
    |(1 / (9192631770 * 1.602176634e-19) : ℝ) - 6.789687e8| ≤ 5e1 ∧
    |(1.380649e-23 / (6.62607015e-34 * 9192631770) : ℝ) - 2.2666653| ≤ 5e-8 ∧
    |(1 / (6.62607015e-34 * (9192631770 : ℝ) ^ 2 * 683)) - 2.614830e10| ≤ 5e3 := by sorry

end SIBrochure
