-- Prove2me | Theorems.Thm_SecretaryWD_Weighted_assigned_class_count
-- name    : SecretaryWD.Weighted.assigned_class_count
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:26:40.729594+00:00
-- url     : https://prove2.me/theorems/576edd56-ec55-4d42-bcd2-8f8275101983
-- title:
--   Lemma 3.1 — a quarter of an occupied value class is assigned
-- statement:
--   Fix a weighted secretary instance with nonnegative agent values and nonnegative, nonincreasing good weights. Let $u_i$ be the number of agents in value class $i$ assigned goods by the sorted offline optimum, and let $f_i$ be the number assigned by the reservation algorithm. If $u_i\ge2$, then expectation over the uniform arrival order and the independent binomial sample size satisfies
--
--   $$\mathbb E[f_i]\ge\frac{u_i}{4}.$$
--
--   This controls how many class-$i$ goods the reservation rule fills before weights and values enter the comparison.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 5, Lemma 3.1

import Mathlib
import Definitions.Def_SecretaryWD_Weighted_Assignment
import Definitions.Def_SecretaryWD_Weighted_ReservationAlgorithm

namespace SecretaryWD.Weighted

/-- Lemma 3.1: a class with at least two optimum goods fills a quarter of them in expectation. -/
theorem assigned_class_count {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w)
    (i : ℤ) (hi : 2 ≤ optimalClassCount (K := K) v i) :
    (optimalClassCount (K := K) v i : ℝ) / 4 ≤
      expectedAssignedClassCount (K := K) v i := by sorry

end SecretaryWD.Weighted
