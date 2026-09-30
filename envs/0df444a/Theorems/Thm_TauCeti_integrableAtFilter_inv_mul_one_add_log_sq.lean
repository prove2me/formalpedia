-- Prove2me | Theorems.Thm_TauCeti_integrableAtFilter_inv_mul_one_add_log_sq
-- name    : TauCeti.integrableAtFilter_inv_mul_one_add_log_sq
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:45:02.07125+00:00
-- url     : https://prove2.me/theorems/f9518491-ed04-4859-ab92-de6ec7e18ced
-- title:
--   Integrability of the logarithmic tail majorant
-- statement:
--   The real function $u\mapsto [u(1+\log u)^2]^{-1}$ is integrable near positive infinity. Equivalently, for some $A>1$,
--
--   $$
--   \int_A^{\infty}\frac{du}{u(1+\log u)^2}<\infty.
--   $$
--
--   This logarithmic tail bound serves as an integrable majorant in summation estimates.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/SpecialFunctions/ImproperIntegrals.lean), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/SpecialFunctions/ImproperIntegrals.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Improper-integral asymptotics and logarithmic decay

This file extends Mathlib's improper-integral estimates with an asymptotic estimate for weighted
integrals and integrability at infinity of `(t (1 + log t) ^ 2)⁻¹`.

## Main declarations

* `TauCeti.integrableAtFilter_inv_mul_one_add_log_sq`: the function
  `t ↦ (t (1 + log t) ^ 2)⁻¹` is integrable at infinity.
* `TauCeti.isLittleO_integral_rpow_sub_one_mul`: a remainder `E t = o(t)` has
  `∫ t in 1..x, t ^ (τ - 1) * E t = o(x ^ (τ + 1))`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

open Asymptotics Filter MeasureTheory Set

theorem TauCeti.integrableAtFilter_inv_mul_one_add_log_sq :
    _root_.MeasureTheory.IntegrableAtFilter (fun u : ℝ ↦ (u * (1 + _root_.Real.log u) ^ 2)⁻¹) _root_.Filter.atTop := by sorry
