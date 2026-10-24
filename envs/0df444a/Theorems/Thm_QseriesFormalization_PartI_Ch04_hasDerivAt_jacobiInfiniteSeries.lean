-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04_hasDerivAt_jacobiInfiniteSeries
-- name    : QseriesFormalization.PartI.Ch04.hasDerivAt_jacobiInfiniteSeries
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:28:57.990868+00:00
-- url     : https://prove2.me/theorems/645019bc-beac-4caa-9135-e33f29ee2425
-- title:
--   Termwise differentiation of the bilateral Jacobi series
-- statement:
--   Let $Q\in\mathbb{C}$ with $|Q|<1$ and $y\in\mathbb{C}$, $y\ne0$. The function $z\mapsto\sum_{n\in\mathbb{Z}}z^nQ^{n^2}$ has complex derivative at $y$ equal to the termwise-differentiated series:
--   $$\frac{d}{dz}\sum_{n\in\mathbb{Z}}z^nQ^{n^2}\Big|_{z=y}=\sum_{n\in\mathbb{Z}}n\,y^{n-1}Q^{n^2}.$$
--   This is used in Chapter 4 to derive Jacobi's identity (Theorem 4.3) by differentiating the triple product.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04_T43.lean#L219-L294

import Definitions.Def_QseriesFormalization_DefCoreQSeries
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

theorem QseriesFormalization.PartI.Ch04.hasDerivAt_jacobiInfiniteSeries (Q : ℂ) (hQ : ‖Q‖ < 1) {y : ℂ} (hy : y ≠ 0) :
    HasDerivAt (fun z => Ch02.jacobiInfiniteSeries Q z)
      (∑' n : ℤ, jacobiSeriesT' Q n y) y := by sorry
