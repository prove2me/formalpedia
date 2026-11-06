-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ArtinSchreier_artinSchreierPolynomial_monic
-- name    : QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial_monic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:07:50.636722+00:00
-- url     : https://prove2.me/theorems/39ffbb69-a1b8-4c4c-81ea-dd0ebe5d008e
-- title:
--   Artin Schreier: artin Schreier Polynomial monic
-- statement:
--   The displayed additive polynomial is monic, independently of its root behavior.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreier.lean#L48-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreier.lean#L48-L55

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ArtinSchreier
open scoped WithZero BigOperators
open Polynomial
variable {F : Type*} [Field F]

theorem QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial_monic (u : F) :
    (artinSchreierPolynomial u).Monic := by sorry
