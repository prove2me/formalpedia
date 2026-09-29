-- Prove2me | Theorems.Thm_Schnir_pi_lower
-- name    : Schnir.pi_lower
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T22:47:32.275981+00:00
-- url     : https://prove2.me/theorems/3e9a1846-3029-4a75-a626-72831bed747c
-- title:
--   Chebyshev-type lower bound $\pi(y)-1\ge 2y/(3\log y)$
-- statement:
--   For every real $y\ge 1000$,
--
--   $$
--   \pi(y)-1 \;\ge\; \frac{2y}{3\log y},
--   $$
--
--   where $\pi(y)$ is the number of primes at most $y$.
--
--   This elementary Chebyshev-type bound supplies all the prime-counting input of the argument: the first-moment lower bound for $r(s)$ and the density of $A$ at moderate scales.
--
--   **Formalization Note** $\pi(y)$ is `Nat.primeCounting ⌊y⌋₊`.
-- source:
--   An explicit elementary constant for sums of primes (unpublished note, September 2026), eq. (3), §1

import Mathlib
import Definitions.Def_Schnir_defs

namespace Schnir

theorem pi_lower (y : ℝ) (hy : 1000 ≤ y) :
    2 * y / (3 * Real.log y) ≤ (Nat.primeCounting ⌊y⌋₊ : ℝ) - 1 := by sorry

end Schnir
