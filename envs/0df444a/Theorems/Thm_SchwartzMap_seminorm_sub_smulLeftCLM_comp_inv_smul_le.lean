-- Prove2me | Theorems.Thm_SchwartzMap_seminorm_sub_smulLeftCLM_comp_inv_smul_le
-- name    : SchwartzMap.seminorm_sub_smulLeftCLM_comp_inv_smul_le
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:45:12.238583+00:00
-- url     : https://prove2.me/theorems/5f862ff9-4171-4155-ad1d-ee0d1a82b85f
-- title:
--   The truncation estimate
-- statement:
--   Let $E,F$ be real normed vector spaces, $f\in\mathcal S(E,F)$ a Schwartz function, and $\chi:E\to\mathbb R$ smooth. Suppose $\|D^i\chi(x)\|\le B_i$ for all $i\ge0$ and $x\in E$, and $\chi=1$ on the open ball of radius $r>0$ about zero. Write $p_{k,n}$ for the standard Schwartz seminorm, and put $\chi_R(x)=\chi(R^{-1}x)$. For $k,n\in\mathbb N$ and $R\ge1$,
--
--   $$
--   p_{k,n}(f-\chi_R f)\le\frac1R\sum_{i=0}^{n}\binom ni(1+B_i)\left(p_{k,n-i}(f)+\frac{p_{k+1,n-i}(f)}r\right).
--   $$
--
--   The estimate quantifies approximation by smooth cutoffs in each Schwartz seminorm.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Distribution/SchwartzSpace/Cutoff.lean#L151-L201), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Distribution/SchwartzSpace/Cutoff.lean#L151-L201

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

theorem SchwartzMap.seminorm_sub_smulLeftCLM_comp_inv_smul_le (hχ : _root_.ContDiff ℝ ∞ χ)
    {B : ℕ → ℝ} (hB : ∀ i x, ‖_root_.iteratedFDeriv ℝ i χ x‖ ≤ B i)
    {r : ℝ} (hr : 0 < r) (hχ1 : ∀ y, ‖y‖ < r → χ y = 1) (f : 𝓢(E, F)) (k n : ℕ) {R : ℝ}
    (hR : 1 ≤ R) :
    _root_.SchwartzMap.seminorm ℝ k n (f - _root_.SchwartzMap.smulLeftCLM F (fun y ↦ χ (R⁻¹ • y)) f) ≤
      (∑ i ∈ _root_.Finset.range (n + 1), (n.choose i : ℝ) * (1 + B i) *
        (_root_.SchwartzMap.seminorm ℝ k (n - i) f + _root_.SchwartzMap.seminorm ℝ (k + 1) (n - i) f / r)) /
        R := by sorry
