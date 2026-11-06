-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_artinSchreier16_bottom_normalizedRefinement
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.artinSchreier16_bottom_normalizedRefinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:17:12.812103+00:00
-- url     : https://prove2.me/theorems/2c729b35-7708-430a-a267-69e3b92faa8a
-- title:
--   F256 Garcia Stichtenoth: artin Schreier16 bottom normalized Refinement
-- statement:
--   The literal additive extension, with normalization checked on the
--   initial field rather than its bottom-subfield copy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionRefinement.lean#L39-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/BasicProjectionRefinement.lean#L39-L53

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionFields
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasicProjectionRefinement
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.artinSchreier16_bottom_normalizedRefinement
    (a : F) (y : E) (hy : y ^ 16 + y = algebraMap F E a)
    (ha : ∀ P : GlobalPlace F256 F, P.order a = -1 ∨ 0 ≤ P.order a) :
    NormalizedRefinement A F E Q ⊥ F⟮y⟯ := by sorry
