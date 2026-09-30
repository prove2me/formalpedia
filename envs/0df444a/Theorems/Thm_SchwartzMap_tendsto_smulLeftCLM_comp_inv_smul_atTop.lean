-- Prove2me | Theorems.Thm_SchwartzMap_tendsto_smulLeftCLM_comp_inv_smul_atTop
-- name    : SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:07:20.135909+00:00
-- url     : https://prove2.me/theorems/61666dd2-b6a4-4bf2-a28c-86ba22e4296d
-- title:
--   Truncations converge in the Schwartz topology
-- statement:
--   Let $E,F$ be real normed vector spaces, $f\in\mathcal S(E,F)$, and let $\chi:E\to\mathbb R$ be smooth, equal to one near zero, with each derivative bounded on $E$. In the Schwartz topology,
--
--   $$
--   \chi(R^{-1}\,\cdot)f\longrightarrow f\qquad(R\to\infty).
--   $$
--
--   This permits the use of expanding smooth cutoffs in arguments involving Schwartz functions.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Distribution/SchwartzSpace/Cutoff.lean#L203-L221), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Distribution/SchwartzSpace/Cutoff.lean#L203-L221

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Cutting off a Schwartz function

Let `χ : E → ℝ` be a smooth compactly supported function that equals `1` near the origin. For a
Schwartz function `f`, the truncations `x ↦ χ (R⁻¹ • x) • f x` are smooth and compactly supported,
and they converge to `f` in the Schwartz topology as `R → ∞`. Consequently the smooth compactly
supported functions are dense in `𝓢(E, F)` when `E` is finite-dimensional.

This is how a statement proved for smooth compactly supported test functions is passed to Schwartz
test functions: any quantity controlled by finitely many Schwartz seminorms (for instance a
weighted sup norm of the Fourier transform) is approximated by its values on the truncations.

The estimate is explicit. Suppose `χ = 1` on the ball of radius `r` and `R ≥ 1`. The difference
`f - χ (R⁻¹ • ·) • f` is `(1 - χ (R⁻¹ • ·)) • f`, which vanishes on the ball of radius `r R`.
Expand its `n`-th derivative by the Leibniz rule. The term in which no derivative falls on the
cutoff is supported where `‖x‖ ≥ r R`, so trading one power of `‖x‖` against `(r R)⁻¹` bounds it by
the `(k + 1, n)` seminorm of `f` divided by `r R`. Every other term carries a derivative of
`χ (R⁻¹ • ·)` of order `i ≥ 1`, which is `R⁻ⁱ` times a derivative of `χ` and hence `O(R⁻¹)`.
Altogether the `(k, n)` seminorm of the difference is `O(R⁻¹)`.

## Main results

* `SchwartzMap.seminorm_sub_smulLeftCLM_comp_inv_smul_le`: the explicit bound
  `seminorm k n (f - χ (R⁻¹ • ·) • f) ≤ K / R` for `R ≥ 1`.
* `SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop`: the truncations converge to `f` in
  `𝓢(E, F)`.
* `SchwartzMap.hasCompactSupport_smulLeftCLM_comp_inv_smul`: the truncations are compactly
  supported.
* `SchwartzMap.dense_hasCompactSupport`: compactly supported functions are dense in
  `𝓢(E, F)` for finite-dimensional `E`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Section 7.1.
-/

 section

open Filter Metric Set
open scoped ContDiff Topology SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace SchwartzMap
end SchwartzMap
section SchwartzMap
open SchwartzMap

variable {χ : E → ℝ}

theorem SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop (hχ : _root_.ContDiff ℝ ∞ χ)
    (hbdd : ∀ i, ∃ B, ∀ x, ‖_root_.iteratedFDeriv ℝ i χ x‖ ≤ B) (hχ1 : χ =ᶠ[𝓝 0] 1) (f : 𝓢(E, F)) :
    _root_.Filter.Tendsto (fun R : ℝ ↦ _root_.SchwartzMap.smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) _root_.Filter.atTop (𝓝 f) := by sorry
