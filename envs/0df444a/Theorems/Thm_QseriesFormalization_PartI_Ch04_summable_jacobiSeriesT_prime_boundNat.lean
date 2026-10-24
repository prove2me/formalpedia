-- Prove2me | Theorems.Thm_QseriesFormalization_PartI_Ch04_summable_jacobiSeriesT_prime_boundNat
-- name    : QseriesFormalization.PartI.Ch04.summable_jacobiSeriesT_prime_boundNat
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T10:33:09.486469+00:00
-- url     : https://prove2.me/theorems/025c7102-f996-434c-9ff2-5ea04fc379e2
-- title:
--   Summability of $\sum n R^{n+1}|Q|^{n^2}$ for $|Q|<1$
-- statement:
--   For $Q\in\mathbb{C}$ with $|Q|<1$ and any real number $R$, the series $\sum_{n\ge0}n\,R^{n+1}\,|Q|^{n^2}$ converges absolutely (the family is summable over $n\in\mathbb{N}$). The Gaussian decay of $|Q|^{n^2}$ beats the geometric growth of $R^n$. This bound is used in Chapter 4 to differentiate the Jacobi series termwise when proving Jacobi's identity for $(q;q)_\infty^3$.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 4. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter04_T43.lean#L58-L125

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

theorem QseriesFormalization.PartI.Ch04.summable_jacobiSeriesT_prime_boundNat (Q : ℂ) (hQ : ‖Q‖ < 1) (R : ℝ) :
    Summable (fun n : ℕ => (n : ℝ) * R ^ (n + 1) * ‖Q‖ ^ (n * n)) := by sorry
