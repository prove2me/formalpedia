-- Prove2me | Theorems.Thm_Schnir_G_lower
-- name    : Schnir.G_lower
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:47:39.415001+00:00
-- url     : https://prove2.me/theorems/0822eeea-6927-4395-9d56-f53fa1a4e0d4
-- title:
--   Lower bound $G_s(z)\ge (\log z)^2/(2C(s))$ for the sieve denominator
-- statement:
--   Let $s$ be a positive even integer and $z>1$ real. With $G_s(z)$ the Selberg sieve denominator and $C(s)=\prod_{p\mid s}\left(1+\frac{p}{(p-1)^2}\right)$,
--
--   $$
--   G_s(z) \;\ge\; \frac{(\log z)^2}{2\,C(s)} .
--   $$
--
--   Combined with the sieve inequality, this bounds the sifted count by $2C(s)\,s/(\log z)^2$ plus the error term.
--
--   **Formalization Note** $G$ and $C$ are `Schnir.G` and `Schnir.C` from `Def_Schnir_defs`.
-- source:
--   An explicit elementary constant for sums of primes (unpublished note, September 2026), eq. (10), §2.2

import Mathlib
import Definitions.Def_Schnir_defs

namespace Schnir

theorem G_lower (s : ℕ) (hs : Even s) (hs0 : 0 < s) (z : ℝ) (hz : 1 < z) :
    (Real.log z) ^ 2 / (2 * C s) ≤ G s z := by sorry

end Schnir
