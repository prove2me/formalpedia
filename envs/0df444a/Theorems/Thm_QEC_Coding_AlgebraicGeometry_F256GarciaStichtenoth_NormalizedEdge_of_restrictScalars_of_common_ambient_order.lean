-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_of_restrictScalars_of_common_ambient_order
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedEdge.of_restrictScalars_of_common_ambient_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:12:24.103092+00:00
-- url     : https://prove2.me/theorems/7231e04a-e434-4881-a80f-0ad83d795f7f
-- title:
--   Normalized Edge: of restrict Scalars of common ambient order
-- statement:
--   Conversely, if both actual edge fields already contain the larger
--   base, the same edge is normalized in its own base model. This is the return
--   direction needed after completing one square of the source pyramid.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RefinementBaseTransport.lean#L94-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RefinementBaseTransport.lean#L94-L105

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrderTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementBaseTransport
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A B F K E : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [_root_.Field F] [_root_.Field K] [_root_.Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [Algebra A F] [IsFractionRing A F] [Algebra A E] [IsScalarTower A F E]
    [Algebra B K] [IsFractionRing B K] [Algebra B E] [IsScalarTower B K E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [Algebra F256 F] [Algebra F256 K] [Algebra F256 E]
    [IsScalarTower F256 F E] [IsScalarTower F256 K E]
    [Module.Finite A (integralClosure A E)] [Module.Finite B (integralClosure B E)]
    [IsDedekindDomain (integralClosure A E)] [IsDedekindDomain (integralClosure B E)]
    [IsFractionRing (integralClosure A E) E] [IsFractionRing (integralClosure B E) E]
    (QA : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
    (QB : IsDedekindDomain.HeightOneSpectrum (integralClosure B E))
local notation "CA" => IntermediateIntegralModels.Model A F E
local notation "CB" => IntermediateIntegralModels.Model B K E
local notation "PA" => IntermediateIntegralModels.prime A F E QA
local notation "PB" => IntermediateIntegralModels.prime B K E QB

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedEdge.of_restrictScalars_of_common_ambient_order
    (hupper : (heightOnePlace (k := F256) (K := E) QA).order =
      (heightOnePlace (k := F256) (K := E) QB).order)
    {J L : IntermediateField K E}
    (h : NormalizedEdge A F E QA (J.restrictScalars F) (L.restrictScalars F)) :
    NormalizedEdge B K E QB J L := by sorry
