-- Prove2me | Theorems.Thm_Schnir_first_moment
-- name    : Schnir.first_moment
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:47:36.461455+00:00
-- url     : https://prove2.me/theorems/7656ea28-4bf4-4e25-ae07-41b7777fcf02
-- title:
--   First moment: $\sum_{s\le x} r(s)\ge x^2/(9(\log x)^2)$
-- statement:
--   Let $r(s)$ be the number of ordered pairs $(p,q)$ of odd primes with $p+q=s$. For every real $x\ge 2000$,
--
--   $$
--   \sum_{0\le s\le x} r(s) \;\ge\; \frac{x^2}{9(\log x)^2}.
--   $$
--
--   This is the first-moment estimate with $c_1=1/9$. Together with the second moment it shows, via Cauchy–Schwarz, that sums of two odd primes have positive density.
--
--   **Formalization Note** The sum runs over integers $0\le s\le\lfloor x\rfloor$. $r$ is `Schnir.r` from `Def_Schnir_defs`.
-- source:
--   An explicit elementary constant for sums of primes (unpublished note, September 2026), eq. (4), §1

import Mathlib
import Definitions.Def_Schnir_defs

namespace Schnir

theorem first_moment (x : ℝ) (hx : 2000 ≤ x) :
    x ^ 2 / (9 * (Real.log x) ^ 2) ≤ ∑ s ∈ Finset.range (⌊x⌋₊ + 1), (r s : ℝ) := by sorry

end Schnir
