-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04_jacobiIdentity
-- name    : QseriesFormalization.PartI.Ch04.jacobiIdentity
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:29:11.255473+00:00
-- url     : https://prove2.me/theorems/bbbf8b76-87e5-4dd9-a9b3-34e10e344e36
-- title:
--   Jacobi's identity: $(q;q)_\infty^3=\sum_{n\ge0}(-1)^n(2n+1)q^{n(n+1)/2}$
-- statement:
--   For every complex $q$ with $|q|<1$,
--   $$\Big(\prod_{k\ge1}(1-q^{k})\Big)^{3}=\sum_{n\ge0}(-1)^n(2n+1)\,q^{n(n+1)/2},$$
--   where the exponent $n(n+1)/2$ is a triangular number. This is Jacobi's identity (Theorem 4.3 in the book), the full identity in the unit disc.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04_T43.lean#L915-L972

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Chapter 4 — Theorem 4.3 (Jacobi's identity)

**Goal**: `(q;q)_∞^3 = ∑_{n≥0} (-1)^n (2n+1) q^{n(n+1)/2}` for `‖q‖ < 1`.

**Strategy** (see `docs/T43_strategy.md`). Parameterise by `Q : ℂ` with
`Q² = q`. JTP at base `Q`:
```
J(Q, z) = ∑_{n∈ℤ} z^n · Q^(n²) = ∏_{n≥1}(1 - Q^(2n))(1 + zQ^(2n-1))(1 + z⁻¹Q^(2n-1)).
```
At `z = -Q` both sides vanish (the `n=1` factor `(1 + z⁻¹Q)|_{z=-Q} = 0`).
Differentiate in `z`, evaluate at `z = -Q`:

* Series:  `dS/dz|_{z=-Q} = -Q⁻¹ · ∑_{n≥0}(2n+1)(-1)^n q^(n(n+1)/2)`.
* Product: `dP/dz|_{z=-Q} = -Q⁻¹ · (q;q)_∞^3`.

JTP gives equality of functions, hence of derivatives. Cancel `-Q⁻¹`.
Lift via `Complex.exists_sq` for the final wrapper.

This module sets up Phase 1: series-side termwise derivative.
-/

open scoped Topology
open Filter

/-! ## Summability of the derivative-bound series

We need summability of the uniform bound
`u(n) := (n.natAbs : ℝ) * R^(n.natAbs+1) * ‖Q‖^(n.natAbs * n.natAbs)`
over `n : ℤ` (and equivalently over `n : ℕ` via the `int_iff_nat_and_neg`
split). The key fact: `‖Q‖^(n*n)` provides Gaussian-style super-exponential
decay that dominates any polynomial-times-geometric bound on the rest.
-/

/-! ## The series derivative theorem

The series side `J(Q, z) = ∑_{n∈ℤ} z^n · Q^{n²}` is differentiable in `z`
on the punctured plane, with derivative given by termwise differentiation.
-/

/-! ## Phase 2: the product-side derivative at `z = -Q`

We factor the JTP infinite product as

  `jacobiInfiniteProduct Q z = (1 + z⁻¹ Q) · P_mod(z)`

where `P_mod` collects the other factors. At `z = -Q` the first factor
vanishes, so `(jacobiInfiniteProduct Q)' (-Q) = ((1 + z⁻¹ Q))' (-Q) · P_mod (-Q)`.

* `(1 + z⁻¹ Q)' (-Q) = -Q⁻¹` (computed below).
* `P_mod (-Q) = (q;q)_∞ ^ 3`  (uses partial-product limit + Ch02 multipliability).
-/

/-! ### Local summability for shifted odd-factor family

`ℂ` is a CommMonoid (not CommGroup) under multiplication, so we cannot use
`Multipliable.tprod_eq_zero_mul` (which needs CommGroup). Instead we use
`tprod_eq_zero_mul'`, which requires multipliability of the shifted family.
We build that from `multipliable_one_add_of_summable` and a local geometric bound. -/

/-! ### Evaluation of `P_mod(-Q) = (q;q)_∞^3` -/

/-! ### Phase 3: series-side reindex

The bilateral series derivative at `z = -Q` reindexes via pairing `n ↔ -1 - n`
to a one-sided sum:
`∑' n : ℤ, jacobiSeriesT' Q n (-Q) = -Q⁻¹ · ∑' n : ℕ, (-1)^n · (2n+1) · Q^(n(n+1))`. -/

/-! ### Phase 3 → 2 bridge: transfer derivative via JTP S = P -/

/-! ### Phase 2 finish: continuity of `P_mod` at `-Q`

Uses `hasProdUniformlyOn_nat_one_add` (from Mathlib) on a closed ball around `-Q`. -/

/-! ### Phase 2 finish: derivative of `jacobiInfiniteProduct` at `-Q` -/

/-! ### Phase 4: Jacobi's identity in Q-parameterised form -/

/-! ### Phase 4: q-parameterised Jacobi's identity -/

theorem QseriesFormalization.PartI.Ch04.jacobiIdentity (q : ℂ) (hq : ‖q‖ < 1) :
    (∏' k : ℕ, (1 - q ^ (k + 1))) ^ 3 =
      ∑' n : ℕ, ((-1) ^ n * (2 * (n : ℂ) + 1) * q ^ (n * (n + 1) / 2)) := by sorry
