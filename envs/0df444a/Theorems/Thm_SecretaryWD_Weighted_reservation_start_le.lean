-- Prove2me | Theorems.Thm_SecretaryWD_Weighted_reservation_start_le
-- name    : SecretaryWD.Weighted.reservation_start_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:26:26.162988+00:00
-- url     : https://prove2.me/theorems/c13f9bd8-2221-4973-ab65-80fe1a33ec28
-- title:
--   Lemma 3.2 — reservation blocks start no later than optimum blocks
-- statement:
--   Fix a weighted secretary instance with nonnegative agent values and nonnegative, nonincreasing good weights. For any arrival order, sample size, and integer value class $i$, let $b_i$ count reservations for classes above $i$, and $o_i$ count optimum assignments to classes above $i$. Then
--
--   $$b_i\le o_i.$$
--
--   Thus the first reserved good of a class is at least as heavy as its first good in the sorted offline assignment.
--
--   **Formalization Note** The integer index includes values below one; for classes above the top populated class both counts are zero.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 5, Lemma 3.2

import Mathlib
import Definitions.Def_SecretaryWD_Weighted_Assignment
import Definitions.Def_SecretaryWD_Weighted_ReservationAlgorithm

namespace SecretaryWD.Weighted

/-- Lemma 3.2: reservations above each class use no more goods than the optimum. -/
theorem reservation_start_le {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w)
    (π : Equiv.Perm (Fin n)) (τ : ℕ) (hτ : τ ≤ n) (i : ℤ) :
    reservationStart v π τ K i ≤ optimalStart (K := K) v i := by sorry

end SecretaryWD.Weighted
