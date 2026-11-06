-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeStalkScalar_SpecMap
-- name    : QEC.Coding.AlgebraicGeometry.schemeStalkScalar_SpecMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:08:02.419311+00:00
-- url     : https://prove2.me/theorems/42469165-df2b-4bd2-a9d5-b622483e4665
-- title:
--   Algebraic Geometry: scheme Stalk Scalar Spec Map
-- statement:
--   On an actual affine chart the structural scalar germ is the literal scalar's stalk image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/StalkScalars.lean#L31-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/StalkScalars.lean#L31-L35

import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Scheme
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_StalkScalars
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.schemeStalkScalar_SpecMap (R S : CommRingCat) (f : R ⟶ S)
    (x : PrimeSpectrum S) (r : R) :
    schemeStalkScalar R (Spec S) (Spec.map f) x r =
      (StructureSheaf.toStalk S x) (f r) := by sorry
