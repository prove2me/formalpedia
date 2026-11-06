-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisWSeed_normalizedRefinement
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWSeed_normalizedRefinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:35:28.113111+00:00
-- url     : https://prove2.me/theorems/c4ac4dd6-327f-4261-94c4-b1d0b6045e9b
-- title:
--   F256 Garcia Stichtenoth: source Galois WSeed normalized Refinement
-- statement:
--   The actual initial rational field has a normalized four-trace
--   refinement over `k(w)`, at the contraction of any final prime of its
--   integral model. The parameter is the literal `w`, not the recursive RHS.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalTraceSeed.lean#L38-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RationalTraceSeed.lean#L38-L50

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RationalTraceSeed
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisWSeed_normalizedRefinement
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A SourceGaloisWField] [IsFractionRing A SourceGaloisWField]
    [Algebra A (RatFunc F256)] [IsScalarTower A SourceGaloisWField (RatFunc F256)]
    [Module.Finite A (integralClosure A (RatFunc F256))]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (RatFunc F256))) :
    NormalizedRefinement A SourceGaloisWField (RatFunc F256) Q ⊥ ⊤ := by sorry
