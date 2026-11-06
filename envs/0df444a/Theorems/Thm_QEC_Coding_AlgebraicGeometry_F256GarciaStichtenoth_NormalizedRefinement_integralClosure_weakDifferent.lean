-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedRefinement_integralClosure_weakDifferent
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedRefinement.integralClosure_weakDifferent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:17:25.954507+00:00
-- url     : https://prove2.me/theorems/332ce227-90d9-4022-8b27-34914ab9c874
-- title:
--   Normalized Refinement: integral Closure weak Different
-- statement:
--   A complete normalized refinement computes the actual original
--   integral closure's different at the supplied final prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RefinementEndpoints.lean#L34-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RefinementEndpoints.lean#L34-L73

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RefinementEndpoints
set_option autoImplicit false
open IntermediateField
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [Module.IsTorsionFree A E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [IsDedekindDomain (integralClosure A E)] [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.endpointAmbientModelTorsionFree

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedRefinement.integralClosure_weakDifferent
    (h : NormalizedRefinement A F E Q ⊥ ⊤) :
    multiplicity Q.asIdeal (differentIdeal A (integralClosure A E)) =
      2 * ((Q.under A).asIdeal.ramificationIdx' Q.asIdeal - 1) := by sorry
