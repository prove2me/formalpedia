-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicForward_normalizedRefinement
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicForward_normalizedRefinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:22:20.32557+00:00
-- url     : https://prove2.me/theorems/8649c27e-3d08-4ee7-9a8c-3687ffc9f707
-- title:
--   F256 Garcia Stichtenoth: source Basic Forward normalized Refinement
-- statement:
--   The four normalized trace steps in the actual forward basic extension.
--   The ambient carrier and its finite separable structure are the already
--   constructed source fields; no different or normalized higher-tower input
--   is required.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionRefinement.lean#L88-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionRefinement.lean#L88-L108

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicForward_normalizedRefinement
    (i : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (SourceBasicForwardField i)] [IsFractionRing A (SourceBasicForwardField i)]
    [Algebra A (SourceBasicForwardExtensionField i)]
    [IsScalarTower A (SourceBasicForwardField i) (SourceBasicForwardExtensionField i)]
    [Module.Finite A (integralClosure A (SourceBasicForwardExtensionField i))]
    (Q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure A (SourceBasicForwardExtensionField i))) :
    NormalizedRefinement A (SourceBasicForwardField i) (SourceBasicForwardExtensionField i)
      Q ⊥ ⊤ := by sorry
