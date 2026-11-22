-- Prove2me | Theorems.Thm_TaylorPolyFarBound
-- name    : TaylorPolyFarBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:13:06.312363+00:00
-- url     : https://prove2.me/theorems/2ab50e2d-f7a1-432b-b653-501b86d86033
-- title:
--   Taylor Poly Far Bound: Taylor Poly Far Bound
-- statement:
--   The sup bound on the degree-`k` Taylor polynomial in the FAR regime, from bounds on its
--   coefficients (paper line 279).
--
--   The paper writes it as `‖P‖_{L^∞(B_r)} ≤ C sum_{j=1}^{k} R_L^{sigma - j} r^j ≤ C max{r,R_L}^sigma`,
--   with "since `sigma - j > 0`" as the whole reason, and closes with `max{r,R_L} ≤ r/tau`.  Here the
--   `max` is already eliminated, as pm-0017 requires: the conclusion is pointwise in `‖y‖` and carries
--   `tau * S ≤ ‖y‖`, which is the paper's far regime.
--
--   That hypothesis is LOAD-BEARING and the statement must not be freed of it: at `‖y‖ = 0` and `j = 0`
--   the underlying power comparison would read `S ^ sigma ≤ 0`, which is false.
--
--   There is no `p`-harmonicity here and no solution: `v` enters only through its jets at the origin,
--   so the node is a statement about a scalar function with controlled coefficients.  `A` is the
--   coefficient constant and `S` the scale at which the coefficients are measured.
--
--   No lower bound on `k` and no positivity of `sigma` are assumed, because neither is needed:
--   `k <= sigma` already forces `sigma > 0` whenever `k >= 1`, and at `k = 0` the polynomial is
--   `v 0 = 0` and the bound reads `0 <= 0`.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TaylorPolyFarBound.lean#L21-L103
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/TaylorPolyFarBound.lean#L21-L103

import Definitions.Def_PHigherOrder_TaylorPoly
import Definitions.Def_PHigherOrder_TaylorPolyFarBound
set_option autoImplicit false

theorem TaylorPolyFarBound (k : ℕ) (σ : ℝ) (hkσ : (k : ℝ) ≤ σ)
    (A : ℝ) (hA : 0 < A) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ∀ (v : Plane → ℝ) (S : ℝ), 0 < S → v 0 = 0 →
      (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ w : Plane,
          |iteratedFDeriv ℝ j v 0 (fun _ => w)| ≤ A * S ^ (σ - (j : ℝ)) * ‖w‖ ^ j) →
      ∀ y : Plane, τ * S ≤ ‖y‖ →
        |TaylorPoly k v 0 y| ≤ (k : ℝ) * A * τ ^ (-σ) * ‖y‖ ^ σ := by sorry
