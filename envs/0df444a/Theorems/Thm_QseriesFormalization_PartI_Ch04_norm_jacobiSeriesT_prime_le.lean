-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04_norm_jacobiSeriesT_prime_le
-- name    : QseriesFormalization.PartI.Ch04.norm_jacobiSeriesT_prime_le
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T10:31:44.795393+00:00
-- url     : https://prove2.me/theorems/08904e64-0f1e-41dc-9706-5d2b11bb1722
-- title:
--   Uniform bound on the termwise derivative of the Jacobi series
-- statement:
--   Let $Q\in\mathbb{C}$, $n\in\mathbb{Z}$, and $y\ne0$ a complex number with $|y|\le R$ and $|y|^{-1}\le R$ for a real $R$. The termwise derivative $T'_n(y)=n\,y^{n-1}Q^{n^2}$ satisfies
--   $$\|T'_n(y)\|\le |n|\,R^{|n|+1}\,\|Q\|^{|n|^2}.$$
--   This bound, uniform for $y$ in an annulus, gives differentiability of the bilateral Jacobi series in Chapter 4.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04_T43.lean#L163-L211

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

theorem QseriesFormalization.PartI.Ch04.norm_jacobiSeriesT_prime_le (Q : ℂ) (n : ℤ) {y : ℂ} {R : ℝ}
    (hy_ne : y ≠ 0) (hyR : ‖y‖ ≤ R) (hyR' : ‖y‖⁻¹ ≤ R) :
    ‖jacobiSeriesT' Q n y‖ ≤
      (n.natAbs : ℝ) * R ^ (n.natAbs + 1) * ‖Q‖ ^ (n.natAbs * n.natAbs) := by sorry
