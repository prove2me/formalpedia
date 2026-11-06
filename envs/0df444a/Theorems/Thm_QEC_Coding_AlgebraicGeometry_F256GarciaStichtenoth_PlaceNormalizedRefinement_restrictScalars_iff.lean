-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_PlaceNormalizedRefinement_restrictScalars_iff
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.PlaceNormalizedRefinement.restrictScalars_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:19:14.872637+00:00
-- url     : https://prove2.me/theorems/e9174467-ab19-4cc9-ac94-43540bdec53c
-- title:
--   Place Normalized Refinement: restrict Scalars iff
-- statement:
--   Exact change of the initial coordinate-window base, using the same
--   ambient place. The intermediate orders are derived from its actual centres.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceRefinement.lean#L44-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/PlaceRefinement.lean#L44-L56

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_AmbientPlaceModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_PlaceRefinement
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open scoped QEC.Coding.AlgebraicGeometry.AmbientPlaceModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
variable (F K : Type*) [_root_.Field F] [_root_.Field K]
    [Algebra F256 F] [Algebra F256 K] [Algebra F K] [Algebra K E] [Algebra F E]
    [IsScalarTower F K E] [IsScalarTower F256 F E] [IsScalarTower F256 K E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (Q : GlobalPlace F256 E)

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.PlaceNormalizedRefinement.restrictScalars_iff
    {J L : IntermediateField K E} :
    PlaceNormalizedRefinement K Q J L ↔
      PlaceNormalizedRefinement F Q (J.restrictScalars F) (L.restrictScalars F) := by sorry
