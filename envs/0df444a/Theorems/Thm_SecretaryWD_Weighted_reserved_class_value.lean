-- Prove2me | Theorems.Thm_SecretaryWD_Weighted_reserved_class_value
-- name    : SecretaryWD.Weighted.reserved_class_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:26:49.523253+00:00
-- url     : https://prove2.me/theorems/04be1d3c-f74d-4ab0-93a7-46670b6053b9
-- title:
--   Lemma 3.3 — an eighth of an occupied class's optimum value
-- statement:
--   Fix a weighted secretary instance with nonnegative agent values and nonnegative, nonincreasing good weights. Let $\mathrm{OPT}_i$ be the sorted offline optimum's value from class $i$, and $R_i$ the reservation algorithm's value from that class. When at least two optimum agents belong to class $i$,
--
--   $$\mathbb E[R_i]\ge\frac18\mathrm{OPT}_i.$$
--
--   This is the weighted class-level estimate used for classes with more than one optimum agent. Here $\mathrm{OPT}_i$ is deterministic, so its expectation equals itself.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 5, Lemma 3.3

import Mathlib
import Definitions.Def_SecretaryWD_Weighted_Assignment
import Definitions.Def_SecretaryWD_Weighted_ReservationAlgorithm

namespace SecretaryWD.Weighted

/-- Lemma 3.3: each class with at least two optimum goods retains an eighth of its value. -/
theorem reserved_class_value {n K : ℕ} (v : Fin n → ℝ) (w : Fin K → ℝ)
    (hv : ∀ e, 0 ≤ v e) (hw : ∀ k, 0 ≤ w k) (hmono : Antitone w)
    (i : ℤ) (hi : 2 ≤ optimalClassCount (K := K) v i) :
    optimalClassValue v w i / 8 ≤ expectedReservedClassValue v w i := by sorry

end SecretaryWD.Weighted
