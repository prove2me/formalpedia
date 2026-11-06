-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeStalkScalar_chart
-- name    : QEC.Coding.AlgebraicGeometry.schemeStalkScalar_chart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:56.375253+00:00
-- url     : https://prove2.me/theorems/e876b0d6-d6ce-4db2-a6ae-f6b85fff0cef
-- title:
--   Algebraic Geometry: scheme Stalk Scalar chart
-- statement:
--   Structural scalar naturality evaluated on a genuine affine chart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/StalkScalars.lean#L38-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Schemes/StalkScalars.lean#L38-L45

import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Scheme
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_StalkScalars
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.schemeStalkScalar_chart (R S : CommRingCat) (Y : Scheme)
    (g : Spec S ⟶ Y) (f : Y ⟶ Spec R) (u : R ⟶ S)
    (h : g ≫ f = Spec.map u) (x : PrimeSpectrum S) (r : R) :
    (g.stalkMap x) (schemeStalkScalar R Y f (g x) r) =
      StructureSheaf.toStalk S x (u r) := by sorry
