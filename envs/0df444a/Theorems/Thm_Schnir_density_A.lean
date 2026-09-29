-- Prove2me | Theorems.Thm_Schnir_density_A
-- name    : Schnir.density_A
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:47:52.726241+00:00
-- url     : https://prove2.me/theorems/163fd1e6-8dd1-4662-82c3-28f2758b2073
-- title:
--   Schnirelmann density $\sigma(A)\ge 1/35000$
-- statement:
--   Let $B=\{(p-3)/2 : p \text{ an odd prime}\}$ and $A=B+B$. The Schnirelmann density
--
--   $$
--   \sigma(A)=\inf_{N\ge 1}\frac{|A\cap\{1,\dots,N\}|}{N}
--   $$
--
--   satisfies
--
--   $$
--   \sigma(A) \;\ge\; \frac{1}{35\,000}.
--   $$
--
--   This bound holds for every $N$, with no "sufficiently large" condition, and it is what the additive argument iterates.
--
--   **Formalization Note** $\sigma$ is Mathlib's `schnirelmannDensity`, with classical decidability. $A$ is `Schnir.A`.
-- source:
--   An explicit elementary constant for sums of primes (unpublished note, September 2026), eq. (16), §5

import Mathlib
import Definitions.Def_Schnir_defs

namespace Schnir

open Classical in
theorem density_A : (1 : ℝ) / 35000 ≤ schnirelmannDensity A := by sorry

end Schnir
