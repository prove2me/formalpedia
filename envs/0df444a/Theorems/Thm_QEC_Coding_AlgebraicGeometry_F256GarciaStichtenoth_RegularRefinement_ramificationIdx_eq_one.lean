-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularRefinement_ramificationIdx_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularRefinement.ramificationIdx_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:19:37.38864+00:00
-- url     : https://prove2.me/theorems/b031849b-c075-41ce-877c-e33e4ab66526
-- title:
--   Regular Refinement: ramification Idx eq one
-- statement:
--   The Regular Refinement construction uses the ramification Idx eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinementRamification.lean#L79-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinementRamification.lean#L79-L101

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinementRamification
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularQuadraticEdge_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularRefinement_le

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
    [IsDedekindDomain (integralClosure A E)] [Module.Finite A (integralClosure A E)]
    [IsFractionRing (integralClosure A E) E]
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A E))
local notation "C" => IntermediateIntegralModels.Model A F E
local notation "P" => IntermediateIntegralModels.prime A F E Q
local notation "R" => heightOnePlace (k := F256) (K := E) Q

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularRefinement.ramificationIdx_eq_one
    {K L : IntermediateField F E} (h : RegularRefinement R K L) :
    letI : Fact (K ≤ L) := ⟨h.le R⟩
    (P K).asIdeal.ramificationIdx' (P L).asIdeal = 1 := by sorry
