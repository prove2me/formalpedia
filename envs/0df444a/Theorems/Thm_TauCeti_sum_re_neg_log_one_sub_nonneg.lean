-- Prove2me | Theorems.Thm_TauCeti_sum_re_neg_log_one_sub_nonneg
-- name    : TauCeti.sum_re_neg_log_one_sub_nonneg
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:06:54.89126+00:00
-- url     : https://prove2.me/theorems/c305b1e8-0369-4125-b228-cacd323f4b1f
-- title:
--   A nonnegative logarithmic combination from boundary positivity
-- statement:
--   Let $I$ be finite, let $c_i\in\mathbb R$ and $m_i\in\mathbb N$, and put $P(z)=\sum_{i\in I}c_i\operatorname{Re}(z^{m_i})$. Assume $P(z)\ge0$ on the unit circle. For every $a\in[0,1)$ and $z\in\mathbb C$ with $|z|\le1$,
--
--   $$
--   \sum_{i\in I}c_i\operatorname{Re}\bigl(-\log(1-az^{m_i})\bigr)\ge0.
--   $$
--
--   This converts trigonometric positivity into a logarithmic inequality used for Euler products.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/SpecialFunctions/Trigonometric/NonnegCombination.lean#L85-L118), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/SpecialFunctions/Trigonometric/NonnegCombination.lean#L85-L118

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Analysis_SpecialFunctions_Trigonometric_NonnegCombination
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Nonnegative trigonometric combinations

This file packages finite trigonometric combinations that are nonnegative on the complex unit
circle. It also transfers their pointwise nonnegativity to the closed unit disk and the Taylor
series of `-log (1 - z)`, giving a reusable logarithmic inequality.

## Main declarations

* `TauCeti.trigonometricCombination` is a finite weighted cosine combination.
* `TauCeti.IsNonnegativeTrigonometricCombination` asserts nonnegativity on the unit circle.
* `TauCeti.trigonometricCombination_nonneg_of_boundary` extends this nonnegativity to the closed
  unit disk.
* `TauCeti.sum_re_neg_log_one_sub_nonneg` transfers boundary nonnegativity to logarithms in the
  open unit disk.

## Provenance

The logarithmic transfer generalizes the private lemma `re_log_comb_nonneg'` in the
`DirichletCharacter` namespace of Mathlib's
`Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, due to Michael Stoll and David Loeffler, from
the fixed `3-4-1` weights to an arbitrary finite nonnegative combination.

This is part of Layer 8.2 of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Complex

noncomputable section

variable {ι : Type*}







variable {s : Finset ι} {c : ι → ℝ} {m : ι → ℕ}

theorem TauCeti.sum_re_neg_log_one_sub_nonneg
    (h : _root_.TauCeti.IsNonnegativeTrigonometricCombination s c m)
    {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ ∑ i ∈ s, c i * (-_root_.Complex.log (1 - a * z ^ m i)).re := by sorry
