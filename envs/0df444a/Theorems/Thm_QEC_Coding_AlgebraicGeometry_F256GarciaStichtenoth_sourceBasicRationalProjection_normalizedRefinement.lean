-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceBasicRationalProjection_normalizedRefinement
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicRationalProjection_normalizedRefinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:17:16.456931+00:00
-- url     : https://prove2.me/theorems/b1a8333a-c6a2-4ff3-86e8-d34e6759822e
-- title:
--   F256 Garcia Stichtenoth: source Basic Rational Projection normalized Refinement
-- statement:
--   Property (A)'s actual normalized chain on a rational basic projection,
--   already embedded in the supplied finite ambient field. The lower order
--   alternative is derived from the source rational function at every place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionRefinement.lean#L72-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionRefinement.lean#L72-L78

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable {E : Type*} [_root_.Field E] [Algebra F256 E]
    (x : E) (hx : Transcendental F256 x) (y : E)
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A F256⟮x⟯] [IsFractionRing A F256⟮x⟯]
    [Algebra A E] [IsScalarTower A F256⟮x⟯ E]
    [FiniteDimensional F256⟮x⟯ E] [Algebra.IsSeparable F256⟮x⟯ E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
include hx

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceBasicRationalProjection_normalizedRefinement
    (hy : y ^ 16 + y = algebraMap F256⟮x⟯ E
      (sourceStepRhs (AdjoinSimple.gen F256 x))) :
    NormalizedRefinement A F256⟮x⟯ E Q ⊥ (F256⟮x⟯)⟮y⟯ := by sorry
