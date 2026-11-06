-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeStalkScalar_comp
-- name    : QEC.Coding.AlgebraicGeometry.schemeStalkScalar_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:08:00.556754+00:00
-- url     : https://prove2.me/theorems/67a561b3-ee54-4497-88ec-441bc54f6c4d
-- title:
--   Algebraic Geometry: scheme Stalk Scalar comp
-- statement:
--   Pullback of scalar germs through an actual scheme morphism.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/StalkScalars.lean#L22-L28
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/StalkScalars.lean#L22-L28

import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Scheme
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_StalkScalars
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.schemeStalkScalar_comp (R : CommRingCat) (X Y : Scheme)
    (g : X ⟶ Y) (f : Y ⟶ Spec R) (x : X) (r : R) :
    (g.stalkMap x) (schemeStalkScalar R Y f (g x) r) =
      schemeStalkScalar R X (g ≫ f) x r := by sorry
