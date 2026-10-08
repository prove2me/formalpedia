-- Prove2me | Theorems.Thm_WeightedMajority_Randomized_pathwise_log_ratio_bound
-- name    : WeightedMajority.Randomized.pathwise_log_ratio_bound
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-08T02:39:59.379976+00:00
-- url     : https://prove2.me/theorems/7f974136-ef75-4d0c-b8de-0b67356b2292
-- title:
--   Pathwise log-ratio loss bound for the weighted-average master (Weighted Majority child B)
-- statement:
--   Child B of the Theorem 6.1 decomposition (Littlestone-Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 240): the deterministic pathwise loss bound for the weighted-average master WMC. Under the WMR model assumptions (0 <= beta < 1, positive initial weights, pool predictions in [0,1], binary labels, update factors satisfying (5.1) in every trial on every sample path), with strictly positive total weight s^(j) = totalWeight ... j omega on every trial, the cumulative absolute loss of the weighted-average prediction gamma, scaled by (1 - beta), is at most ln(w_init / w_fin), where w_init and w_fin are the total weights before the first and after the last trial.
--
--   Proof strategy (for the prover of this node): from the (5.1)-upper bound in IsWMRModel, s^(j+1) = sum_i F_j_i w_i <= sum_i (1-(1-beta)|x_i-rho|) w_i; by the convex-combination triangle inequality (child A, WeightedMajority.Randomized.convex_abs_weighted_bound), s^(j)|gamma^j - rho^j| <= sum_i w_i|x_i - rho|, so s^(j+1) <= s^(j)(1-(1-beta)|gamma^j - rho^j|). Since all s^(j) > 0, ln(s^(j)/s^(j+1)) >= -ln(1-(1-beta)|gamma^j - rho^j|) >= (1-beta)|gamma^j - rho^j| by Real.log_le_sub_one_of_pos; summing over j telescopes to ln(s^0/s^t). Pure real analysis, no probability; the a.e. positivity hypothesis is discharged in the theorem_6_1 assembly from w_fin > 0 a.s. by backward induction (F >= 0, so a zero total propagates forward).
--
--   Degenerate cases: n = 0 makes hpos unsatisfiable (totalWeight = 0), so the theorem holds vacuously; t = 0 gives 0 <= ln(1) = 0. No hidden non-degeneracy hypothesis is missing.
-- source:
--   weightedmajority6_triage_20261007.md section 5, child B of the theorem_6_1 (0daad7b8) decomposition; Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 240

import Mathlib
import Definitions.Def_WeightedMajority_Randomized_WMRModel
set_option autoImplicit false

namespace WeightedMajority.Randomized

/-- Pathwise log-ratio bound (child B of the `theorem_6_1` decomposition,
Littlestone-Warmuth 1994, p. 240): under the WMR model assumptions, with
strictly positive total weight on every trial, the cumulative absolute loss
of the weighted-average master, scaled by `(1 - beta)`, is at most
`Real.log (w_init / w_fin)`. Per trial, the (5.1)-upper bound in `hM` gives
`s^(j+1) <= s^j * (1 - (1-beta)*|gamma^j - rho^j|)` via the convex-combination
triangle inequality (child A, convex_abs_weighted_bound); then
`Real.log_le_sub_one_of_pos` turns the multiplicative drop into the additive
bound `(1-beta)*|gamma^j - rho^j| <= log (s^j / s^(j+1))`, and the drops
telescope to `log (s^0 / s^t)`. -/
theorem pathwise_log_ratio_bound {Omega : Type*} [MeasurableSpace Omega] {n t : Nat}
    (beta : Real) (w1 : Fin n -> Real)
    (F : Nat -> Fin n -> Real -> Real -> Real)
    (x : Nat -> Fin n -> Omega -> Real)
    (rho lam : Nat -> Omega -> Real)
    (hM : IsWMRModel t beta w1 F x rho lam)
    (hpos : forall (j : Nat), j <= t ->
      forall (omega : Omega), 0 < totalWeight w1 F x rho j omega) :
    forall (omega : Omega), (1 - beta)
        * Finset.sum (Finset.range t)
            (fun j => abs (gamma w1 F x rho j omega - rho j omega))
      <= Real.log (totalWeight w1 F x rho 0 omega / totalWeight w1 F x rho t omega) :=
  by sorry

end WeightedMajority.Randomized
