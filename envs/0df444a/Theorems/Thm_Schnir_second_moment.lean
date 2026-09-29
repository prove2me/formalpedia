-- Prove2me | Theorems.Thm_Schnir_second_moment
-- name    : Schnir.second_moment
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:48:03.026022+00:00
-- url     : https://prove2.me/theorems/98a5b1f2-7144-43ed-b139-904411db5bfa
-- title:
--   Second moment: $\sum_{s\le x} r(s)^2\le 860\,x^3/(\log x)^4$
-- statement:
--   For every real $x\ge e^{2000}$,
--
--   $$
--   \sum_{0\le s\le x} r(s)^2 \;\le\; 860\,\frac{x^3}{(\log x)^4}.
--   $$
--
--   This is the second-moment estimate with $c_2=860$ and $x_0=e^{2000}$.
--
--   **Formalization Note** The sum runs over integers $0\le s\le\lfloor x\rfloor$.
-- source:
--   An explicit elementary constant for sums of primes (unpublished note, September 2026), eq. (14), §4

import Mathlib
import Definitions.Def_Schnir_defs

namespace Schnir

theorem second_moment (x : ℝ) (hx : Real.exp 2000 ≤ x) :
    ∑ s ∈ Finset.range (⌊x⌋₊ + 1), (r s : ℝ) ^ 2 ≤ 860 * x ^ 3 / (Real.log x) ^ 4 := by sorry

end Schnir
