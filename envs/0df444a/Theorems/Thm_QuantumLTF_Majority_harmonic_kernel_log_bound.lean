-- Prove2me | Theorems.Thm_QuantumLTF_Majority_harmonic_kernel_log_bound
-- name    : QuantumLTF.Majority.harmonic_kernel_log_bound
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-17T00:58:28.965135+00:00
-- url     : https://prove2.me/theorems/87397e81-cf56-446d-8224-3a26aecfd37d
-- title:
--   Logarithmic bound for the symmetric harmonic kernel
-- statement:
--   There is a universal constant $H>0$ such that, for every $r\ge3$,
--
--   $$
--   \sum_{t=0}^{r}\frac{r}{(t+1)(r-t+1)}\le H\log r.
--   $$
--
--   Using partial fractions, each summand is bounded by a constant multiple of $1/(t+1)+1/(r-t+1)$, so the sum is controlled by the harmonic series.
-- source:
--   Elementary harmonic-sum estimate used to sum the pointwise objective bounds in Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Section 4.2, Lemma 4.3.

import Mathlib

namespace QuantumLTF.Majority

theorem harmonic_kernel_log_bound : ∃ H : ℝ, 0 < H ∧ ∀ r : ℕ, 3 ≤ r → ∑ t : Fin (r+1), (r : ℝ) / (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ)) ≤ H * Real.log r := by sorry

end QuantumLTF.Majority
