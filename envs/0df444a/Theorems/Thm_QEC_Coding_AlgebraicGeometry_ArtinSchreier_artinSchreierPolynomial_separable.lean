-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_ArtinSchreier_artinSchreierPolynomial_separable
-- name    : QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial_separable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:07:56.631888+00:00
-- url     : https://prove2.me/theorems/6e40b6e4-45d7-47de-913a-695447261032
-- title:
--   Artin Schreier: artin Schreier Polynomial separable
-- statement:
--   In characteristic two, the tower's additive polynomial is separable because its
--   derivative is one.  This is distinct from the valuation-based irreducibility work.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreier.lean#L59-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ArtinSchreier.lean#L59-L68

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ArtinSchreier
open scoped WithZero BigOperators
open Polynomial
variable {F : Type*} [Field F]

theorem QEC.Coding.AlgebraicGeometry.ArtinSchreier.artinSchreierPolynomial_separable [CharP F 2] (u : F) :
    (artinSchreierPolynomial u).Separable := by sorry
