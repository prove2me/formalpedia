-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_range_iff
-- name    : QEC.Coding.AlgebraicGeometry.kaehler_field_map_range_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:09:51.463147+00:00
-- url     : https://prove2.me/theorems/7e4d29e0-9207-4786-bca4-4395bfdb2044
-- title:
--   Algebraic Geometry: kaehler field map range iff
-- statement:
--   A genuine surjective intermediate ring map preserves the differential image in the field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/KaehlerMapImage.lean#L37-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/KaehlerMapImage.lean#L37-L46

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

theorem QEC.Coding.AlgebraicGeometry.kaehler_field_map_range_iff (h : Function.Surjective (algebraMap A B))
    (ω : KaehlerDifferential R K) :
    ω ∈ (KaehlerDifferential.map R R A K).range ↔
      ω ∈ (KaehlerDifferential.map R R B K).range := by sorry
