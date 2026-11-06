-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_injective_localization
-- name    : QEC.Coding.AlgebraicGeometry.kaehler_field_map_injective_localization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:10:39.288407+00:00
-- url     : https://prove2.me/theorems/24bc90ed-ef2a-4492-9cb5-475e044dd06d
-- title:
--   Algebraic Geometry: kaehler field map injective localization
-- statement:
--   Actual Kahler localization and its inverted denominators transport a proved affine differential injection to the localized ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerInjective.lean#L106-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/AffineKaehlerInjective.lean#L106-L126

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.Algebra.GroupWithZero.Action.Units
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing K]
variable [Algebra R A] [Algebra R B] [Algebra R K]
variable [Algebra A B] [Algebra B K] [Algebra A K]
variable [IsScalarTower R A B] [IsScalarTower R B K] [IsScalarTower R A K]
variable [IsScalarTower A B K]
variable [SMulCommClass R A B] [SMulCommClass R A K] [SMulCommClass R B K]

theorem QEC.Coding.AlgebraicGeometry.kaehler_field_map_injective_localization
    (S : Submonoid A) [IsLocalization S B]
    (hA : Function.Injective (KaehlerDifferential.map R R A K)) :
    Function.Injective (KaehlerDifferential.map R R B K) := by sorry
