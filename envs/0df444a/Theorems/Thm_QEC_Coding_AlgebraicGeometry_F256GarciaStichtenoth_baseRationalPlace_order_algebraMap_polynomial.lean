-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_baseRationalPlace_order_algebraMap_polynomial
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.baseRationalPlace_order_algebraMap_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:28:52.887559+00:00
-- url     : https://prove2.me/theorems/db81d42c-dd28-454c-83ce-01ed8b247a1a
-- title:
--   F256 Garcia Stichtenoth: base Rational Place order algebra Map polynomial
-- statement:
--   At the rational place `X=a`, the order of a nonzero polynomial is its
--   root multiplicity at the literal point `a`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasePlaces.lean#L243-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasePlaces.lean#L243-L256

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Mathlib.RingTheory.Polynomial.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.baseRationalPlace_order_algebraMap_polynomial
    (a : BasePoint) (p : F256[X]) (hp : p ≠ 0) :
    (baseRationalPlace a).place.order
        (algebraMap F256[X] (RatFunc F256) p) =
      (p.rootMultiplicity (a : F256) : ℤ) := by sorry
