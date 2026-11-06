-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicReverse_normalizedRefinement
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicReverse_normalizedRefinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:22:39.290863+00:00
-- url     : https://prove2.me/theorems/b2c557cb-59ff-4410-96a1-2f37e7981000
-- title:
--   F256 Garcia Stichtenoth: source Basic Reverse normalized Refinement
-- statement:
--   The inverse-coordinate orientation gives a normalized chain on the
--   same source basic cell, now over the actual reverse rational field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionRefinement.lean#L112-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionRefinement.lean#L112-L135

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicReverse_normalizedRefinement
    (i : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (SourceBasicReverseField i)] [IsFractionRing A (SourceBasicReverseField i)]
    [Algebra A (SourceBasicReverseExtensionField i)]
    [IsScalarTower A (SourceBasicReverseField i) (SourceBasicReverseExtensionField i)]
    [Module.Finite A (integralClosure A (SourceBasicReverseExtensionField i))]
    (Q : IsDedekindDomain.HeightOneSpectrum
      (integralClosure A (SourceBasicReverseExtensionField i))) :
    NormalizedRefinement A (SourceBasicReverseField i) (SourceBasicReverseExtensionField i)
      Q ⊥ ⊤ := by sorry
