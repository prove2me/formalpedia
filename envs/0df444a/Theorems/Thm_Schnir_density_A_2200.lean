-- Prove2me | Theorems.Thm_Schnir_density_A_2200
-- name    : Schnir.density_A_2200
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T07:04:40.372289+00:00
-- url     : https://prove2.me/theorems/0c8e8db9-70dd-454a-9bd7-363a7ba01a09
-- title:
--   The Schnirelmann density of the two-prime sumset is at least $1/2200$
-- statement:
--   The Schnirelmann density of the two-odd-prime sumset is at least $1/2200$.
--
--   Let $B=\{(p-3)/2 : p$ an odd prime$\}$ and $A=B+B$ (pointwise sumset), so that $t\in A$ exactly when $2t+6$ is a sum of two odd primes. Then
--
--   $$\sigma(A)\;\ge\;\frac{1}{2200},$$
--
--   where $\sigma(S)=\inf_{n\ge 1}|S\cap\{1,\dots,n\}|/n$ is the Schnirelmann density.
--
--   This is the sharpest density input currently available for the odd-Goldbach campaign: it strengthens the published bound `Schnir.density_A` ($1/35000$) by a factor of sixteen, and is the number that the accepted proof of `odd_sum_le_6101_primes` derives internally (its parts a–d: a first moment for the representation count $r(s)$ from the prime-counting lower bound, Abel summation for the weight $\log^2 s/s$, and a weighted Cauchy–Schwarz against the Selberg-type pointwise bound and the mean square of the singular series). Publishing it as a standalone theorem makes it importable: combined with Mann's theorem $\sigma(D+E)\ge\min(1,\sigma(D)+\sigma(E))$, it yields $\sigma(1100A)\ge 1/2$ and hence that every odd number greater than $1$ is a sum of at most $4401$ primes, improving on $6101$.
--
--   **Formalization Note** $A$ and $B$ are the definitions of `Schnir.A` and `Schnir.B` from `Def_Schnir_defs`; the `DecidablePred` instance is provided classically (`open Classical`). The Lean derivation is extracted verbatim (parts a–d) from the accepted solution dfb232e4 of `odd_sum_le_6101_primes` by xuanji, contributed there under Apache 2.0, and reuses the proved platform theorems `Schnir.pi_lower`, `Schnir.pointwise_bound`, and `Schnir.C_mean`.
-- source:
--   An explicit elementary constant for sums of primes (unpublished note, September 2026), Sections 5-6 (density bound sigma(A) >= 1/2200); Lean derivation extracted from submission dfb232e4 (odd_sum_le_6101_primes, by xuanji), parts a-d

import Mathlib
import Definitions.Def_Schnir_defs

namespace Schnir

open Classical in
theorem density_A_2200 : (1 : ℝ) / 2200 ≤ schnirelmannDensity A := by sorry

end Schnir
