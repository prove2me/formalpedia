-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_comp
-- name    : QEC.Coding.AlgebraicGeometry.kaehler_field_map_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:05:43.04721+00:00
-- url     : https://prove2.me/theorems/d0ca65bb-4c24-4a0c-bca0-b1ae5a513536
-- title:
--   Algebraic Geometry: kaehler field map comp
-- statement:
--   Universal field differential maps compose along compatible scalar towers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/KaehlerMapImage.lean#L21-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/KaehlerMapImage.lean#L21-L34

import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_KaehlerMapImage
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
variable [Algebra R A] [Algebra R B] [Algebra R K]
variable [Algebra A B] [Algebra B K] [Algebra A K]
variable [IsScalarTower R A B] [IsScalarTower R B K] [IsScalarTower R A K]
variable [IsScalarTower A B K]
variable [SMulCommClass R A B] [SMulCommClass R A K] [SMulCommClass R B K]

theorem QEC.Coding.AlgebraicGeometry.kaehler_field_map_comp (η : KaehlerDifferential R A) :
    KaehlerDifferential.map R R A K η =
      KaehlerDifferential.map R R B K (KaehlerDifferential.map R R A B η) := by sorry
