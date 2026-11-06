-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedRefinement_integralClosure_differentialGeneratorOrder
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedRefinement.integralClosure_differentialGeneratorOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:17:48.696554+00:00
-- url     : https://prove2.me/theorems/ade8fee2-0b35-4b58-8a17-68956a9663b8
-- title:
--   Normalized Refinement: integral Closure differential Generator Order
-- statement:
--   The full chain's order formula on the original lower fraction field
--   and upper integral closure, with the redundant lattice endpoints removed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedDifferentialRefinement.lean#L135-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedDifferentialRefinement.lean#L135-L207

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialStepOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedDifferentialRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open IntermediateField QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped QEC.Coding.AlgebraicGeometry.IntermediateIntegralModels
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
variable (A F E : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [_root_.Field F] [_root_.Field E] [Algebra A F] [IsFractionRing A F]
    [Algebra F E] [Algebra A E] [IsScalarTower A F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    [Algebra F256 F] [Algebra F256 E] [IsScalarTower F256 F E]
    [Algebra (RatFunc F256) F] [Algebra (RatFunc F256) E]
    [IsScalarTower F256 (RatFunc F256) F] [IsScalarTower F256 (RatFunc F256) E]
    [IsScalarTower (RatFunc F256) F E]
    [FiniteDimensional (RatFunc F256) F] [Algebra.IsSeparable (RatFunc F256) F]
    [Module.Finite A (integralClosure A E)]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.intermediateRationalConstantTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.intermediateRationalRelativeTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.intermediateConstantRelativeTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.intermediateRationalFinite
attribute [local instance] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.intermediateRationalSeparable
local notation "g" => intermediateDifferentialGeneratorOrder A F E Q

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedRefinement.integralClosure_differentialGeneratorOrder
    [FiniteDimensional (RatFunc F256) E] [Algebra.IsSeparable (RatFunc F256) E]
    [Module.IsTorsionFree A E] [IsDedekindDomain (integralClosure A E)]
    [IsFractionRing (integralClosure A E) E]
    (h : NormalizedRefinement A F E Q ⊥ ⊤) :
    differentialOrder (heightOnePlace (k := F256) (K := E) Q)
      (functionFieldDifferentialGenerator (k := F256) (F := E))
      functionFieldDifferentialGenerator_ne_zero =
    ((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) *
      differentialOrder (heightOnePlace (k := F256) (K := F) (Q.under A))
        (functionFieldDifferentialGenerator (k := F256) (F := F))
        functionFieldDifferentialGenerator_ne_zero +
      2 * (((Q.under A).asIdeal.ramificationIdx' Q.asIdeal : ℤ) - 1) := by sorry
