-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_NormalizedEdge_differentialGeneratorOrder
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedEdge.differentialGeneratorOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:11:59.559231+00:00
-- url     : https://prove2.me/theorems/5de009a4-9707-4d67-8cbd-cc0873987e67
-- title:
--   Normalized Edge: differential Generator Order
-- statement:
--   The Normalized Edge construction uses the differential Generator Order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedDifferentialRefinement.lean#L67-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/NormalizedDifferentialRefinement.lean#L67-L109

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialStepOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedCompositumEdges
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_NormalizedDifferentialRefinement
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
omit [IsScalarTower F256 (RatFunc F256) F]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.NormalizedEdge.differentialGeneratorOrder
    {K L : IntermediateField F E} [Fact (K ≤ L)]
    (h : NormalizedEdge A F E Q K L) :
    g L = ((P K).asIdeal.ramificationIdx' (P L).asIdeal : ℤ) * g K +
      2 * (((P K).asIdeal.ramificationIdx' (P L).asIdeal : ℤ) - 1) := by sorry
