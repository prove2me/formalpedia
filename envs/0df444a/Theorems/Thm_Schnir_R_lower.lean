-- Prove2me | Theorems.Thm_Schnir_R_lower
-- name    : Schnir.R_lower
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:47:56.612994+00:00
-- url     : https://prove2.me/theorems/f556784f-526e-4aa3-a8bd-cc8e8712b0af
-- title:
--   Sums of two odd primes have positive density: $R(x)\ge x/69660$
-- statement:
--   Let $R(x)=\#\{0\le s\le x : r(s)>0\}$ be the number of integers up to $x$ that are sums of two odd primes. For every real $x\ge e^{2000}$,
--
--   $$
--   R(x) \;\ge\; \frac{x}{69\,660}.
--   $$
--
--   This follows from the first and second moments by Cauchy–Schwarz, with $69\,660=9^2\cdot 860$.
--
--   **Formalization Note** The count is over integers $0\le s\le\lfloor x\rfloor$.
-- source:
--   An explicit elementary constant for sums of primes (unpublished note, September 2026), eq. (15), §4

import Mathlib
import Definitions.Def_Schnir_defs

namespace Schnir

theorem R_lower (x : ℝ) (hx : Real.exp 2000 ≤ x) :
    x / 69660 ≤ (((Finset.range (⌊x⌋₊ + 1)).filter (fun s => 0 < r s)).card : ℝ) := by sorry

end Schnir
