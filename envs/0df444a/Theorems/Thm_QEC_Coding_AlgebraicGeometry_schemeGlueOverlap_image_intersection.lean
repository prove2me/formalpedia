-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeGlueOverlap_image_intersection
-- name    : QEC.Coding.AlgebraicGeometry.schemeGlueOverlap_image_intersection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:00:34.4349+00:00
-- url     : https://prove2.me/theorems/786b0a37-bc99-46a7-97c5-9709cf261762
-- title:
--   Algebraic Geometry: scheme Glue Overlap image intersection
-- statement:
--   The Algebraic Geometry construction uses the scheme Glue Overlap image intersection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/SchemeOverlapImages.lean#L17-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/SchemeOverlapImages.lean#L17-L31

import Mathlib.AlgebraicGeometry.Gluing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_SchemeOverlapImages
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
universe u
attribute [local instance] QEC.Coding.AlgebraicGeometry.schemeGlueOverlapOpenImmersion

theorem QEC.Coding.AlgebraicGeometry.schemeGlueOverlap_image_intersection (D : Scheme.GlueData.{u}) (i j : D.J) :
    (D.f i j ≫ D.ι i).opensRange = (D.ι i).opensRange ⊓ (D.ι j).opensRange := by sorry
