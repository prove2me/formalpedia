-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04_jacobiSeriesT_prime_pair_at_negQ
-- name    : QseriesFormalization.PartI.Ch04.jacobiSeriesT_prime_pair_at_negQ
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:31:12.327957+00:00
-- url     : https://prove2.me/theorems/06a5c34e-f054-44e2-b3be-5a7788ea5c67
-- title:
--   Paired derivative terms of the Jacobi series at $z=-Q$
-- statement:
--   Let $Q\in\mathbb{C}$, $Q\ne0$, and $n\in\mathbb{N}$. Let $T'_m(z)=m\,z^{m-1}Q^{m^2}$ be the termwise $z$-derivative of the $m$-th term of the bilateral Jacobi series. Then
--   $$T'_n(-Q)+T'_{-(1+n)}(-Q)=-Q^{-1}\,(-1)^n(2n+1)\,Q^{n(n+1)}.$$
--   This pairing of the terms $n$ and $-1-n$ at $z=-Q$ is used in Chapter 4's proof of Jacobi's identity (Theorem 4.3).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04_T43.lean#L527-L573

import Definitions.Def_QseriesFormalization_Chapter04_T43
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

open QseriesFormalization
open QseriesFormalization.PartI
open QseriesFormalization.PartI.Ch04

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

theorem QseriesFormalization.PartI.Ch04.jacobiSeriesT_prime_pair_at_negQ (Q : ℂ) (hQ : Q ≠ 0) (n : ℕ) :
    jacobiSeriesT' Q n (-Q) + jacobiSeriesT' Q (-(1 + (n : ℤ))) (-Q) =
      -Q⁻¹ * ((-1) ^ n * (2 * (n : ℂ) + 1) * Q ^ ((n : ℕ) * (n + 1))) := by sorry
