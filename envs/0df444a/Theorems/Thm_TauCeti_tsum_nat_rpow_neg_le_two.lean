-- Prove2me | Theorems.Thm_TauCeti_tsum_nat_rpow_neg_le_two
-- name    : TauCeti.tsum_nat_rpow_neg_le_two
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:39:30.577296+00:00
-- url     : https://prove2.me/theorems/e025d232-bf7a-4b0d-8674-08b4cd197064
-- title:
--   The p-series over ℕ is at most 2 beyond exponent two
-- statement:
--   For every real exponent $t\ge2$, the positive-term series satisfies
--
--   $$
--   \sum_{m=1}^{\infty}m^{-t}\le2.
--   $$
--
--   This gives a uniform numerical majorant for prime-sum comparisons in this range.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/PSeries.lean#L36-L54), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/PSeries.lean#L36-L54

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ZetaValues

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# A clean constant bound for the `p`-series beyond exponent two

`∑' m : ℕ, m ^ (-t) ≤ 2` for every real `t ≥ 2`. Mathlib supplies the exact value at the endpoint,
`ζ (2) = π ^ 2 / 6`, and summability throughout `t > 1`, but no inequality valid across a range of
exponents; that is what this file adds.

The bound is deliberately lossy. The supremum over `t ≥ 2` is `ζ (2) = 1.6449…`, so `2` gives away
about 18%. A round constant is the useful thing to expose: consumers carry it through chains of
inequalities and none of them wants `π` in the goal.

Nothing here is specific to any application, and the file contains no number theory. The `m = 0`
term is `0`, by the junk value of `0 ^ (-t)`.

## Main results

* `TauCeti.tsum_nat_rpow_neg_le_two` — `∑' m : ℕ, m ^ (-t) ≤ 2` for `2 ≤ t`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

theorem TauCeti.tsum_nat_rpow_neg_le_two {t : ℝ} (ht : 2 ≤ t) : ∑' m : ℕ, (m : ℝ) ^ (-t) ≤ 2 := by sorry
