-- Prove2me | Theorems.Thm_TauCeti_summable_mul_norm_pow_succ
-- name    : TauCeti.summable_mul_norm_pow_succ
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:31:28.870703+00:00
-- url     : https://prove2.me/theorems/61ab02f5-5bb7-4ce5-860c-ab8b8d1df822
-- title:
--   Summability of a weighted geometric family
-- statement:
--   Let $\iota$ be an index set, let $r_i$ lie in a seminormed additive group, and let $w_i\in\mathbb R$. Suppose the family $(w_i\|r_i\|)_{i\in\iota}$ is summable, $\|r_i\|<1$ whenever $w_i\ne0$, and there is $\varepsilon>0$ such that $\|r_i\|\le1-\varepsilon$ for all but finitely many indices with $w_i\ne0$. Then
--
--   $$
--   \bigl(w_i\|r_i\|^{e+1}\bigr)_{(i,e)\in\iota\times\mathbb N}\quad\text{is summable}.
--   $$
--
--   The weights may have either sign; no bound on $r_i$ is needed when $w_i=0$.
--
--   This permits simultaneous summation over an arbitrary index set and the positive powers of a uniformly contracting family.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Topology/Algebra/InfiniteSum/Real.lean#L30-L84) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Topology/Algebra/InfiniteSum/Real.lean#L30-L84

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Weighted geometric majorants over an index and an exponent

For a family `r : ι → E` in a seminormed additive group whose norms are less than one, and
eventually at most `1 - ε`, wherever the weight `w` is nonzero, the double family
`(i, e) ↦ w i * ‖r i‖ ^ (e + 1)` is summable over `ι × ℕ` as soon as `i ↦ w i * ‖r i‖` is
summable. Each fibre is geometric, so it
sums to `w i * ‖r i‖ / (1 - ‖r i‖)`, and the eventual bound keeps `1 / (1 - ‖r i‖)` under `ε⁻¹`
off a finite set; a fibre where the weight vanishes is zero and needs no bound at all.

## Main results

* `TauCeti.summable_mul_norm_pow_succ`: the weighted double family is summable over `ι × ℕ`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

theorem TauCeti.summable_mul_norm_pow_succ {ι E : Type*} [_root_.SeminormedAddGroup E] {r : ι → E} {w : ι → ℝ}
    (hbd : ∃ ε > 0, ∀ᶠ i in _root_.Filter.cofinite, w i ≠ 0 → ‖r i‖ ≤ 1 - ε)
    (hwr : _root_.Summable fun i ↦ w i * ‖r i‖) (h1 : ∀ i, w i ≠ 0 → ‖r i‖ < 1) :
    _root_.Summable fun ie : ι × ℕ ↦ w ie.1 * ‖r ie.1‖ ^ (ie.2 + 1) := by sorry
