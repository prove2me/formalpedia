-- Prove2me | Theorems.Thm_QuantumLTF_Majority_pointwise_correction_bound_to_log_energy
-- name    : QuantumLTF.Majority.pointwise_correction_bound_to_log_energy
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-17T17:39:35.037713+00:00
-- url     : https://prove2.me/theorems/83ca5ed7-1438-4b57-a3a1-23f7238827b7
-- title:
--   Pointwise correction bounds sum to logarithmic energy
-- statement:
--   Suppose the total correction energy at degree $t$ is bounded pointwise by
--
--   $$
--   e_t\le D\,\frac{r}{(t+1)(r-t+1)}.
--   $$
--
--   Then the sum over all degrees is at most $DH\log r$ for a universal constant $H$. This is the final harmonic summation in the proof of equation (126), after the Appendix C.2 pointwise correction estimate and Lemma C.4 have been applied.
-- source:
--   Krivcenko, Nguyen, de Wolf, arXiv:2609.40331v3, Appendix C.2, proof of equation (126), following Lemma C.4.

import Mathlib

namespace QuantumLTF.Majority

theorem pointwise_correction_bound_to_log_energy : ∃ H : ℝ, 0 < H ∧ ∀ r : ℕ, 3 ≤ r → ∀ D : ℝ, 0 ≤ D → ∀ e : Fin (r+1) → ℝ, (∀ t : Fin (r+1), e t ≤ D * (r : ℝ) / (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ))) → (∑ t : Fin (r+1), e t) ≤ D * H * Real.log r := by sorry

end QuantumLTF.Majority
