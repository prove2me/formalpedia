-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ArtinSchreier_val_of_frobenius_fixed
-- name    : QEC.Coding.AlgebraicGeometry.ArtinSchreier.val_of_frobenius_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:09:32.622588+00:00
-- url     : https://prove2.me/theorems/1557163c-2ee7-491c-a30c-4f61ef23579a
-- title:
--   Artin Schreier: val of frobenius fixed
-- statement:
--   A Frobenius-fixed element (`c³² = c`) has valuation `0` (iff `c = 0`)
--   or `1`: applying `ν` gives `(ν c)³² = ν c`, i.e. `32·log (ν c) = log (ν c)`
--   in `ℤᵐ⁰`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreier.lean#L78-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreier.lean#L78-L94

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ArtinSchreier
open scoped WithZero BigOperators
open Polynomial
variable {F : Type*} [Field F]

theorem QEC.Coding.AlgebraicGeometry.ArtinSchreier.val_of_frobenius_fixed (ν : Valuation F ℤᵐ⁰) {c : F} (hc : c ^ 32 = c) :
    ν c = 0 ∨ ν c = 1 := by sorry
