-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_normalizedEdge_refl
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.normalizedEdge_refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:13:20.972897+00:00
-- url     : https://prove2.me/theorems/45efceb3-6042-4bcc-a211-320cb56357a1
-- title:
--   F256 Garcia Stichtenoth: normalized Edge refl
-- statement:
--   The literal identity edge is available at every intermediate field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedCompositumEdges.lean#L82-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedCompositumEdges.lean#L82-L87

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_IntermediateIntegralModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticCompositumCell
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_RelativeTower
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
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
local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.normalizedEdge_refl (K : IntermediateField F E) :
    NormalizedEdge A F E Q K K := by sorry
