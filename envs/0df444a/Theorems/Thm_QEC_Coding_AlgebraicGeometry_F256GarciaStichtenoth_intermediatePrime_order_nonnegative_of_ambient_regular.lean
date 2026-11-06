-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_intermediatePrime_order_nonnegative_of_ambient_regular
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.intermediatePrime_order_nonnegative_of_ambient_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:19:31.208606+00:00
-- url     : https://prove2.me/theorems/14d30150-c8fa-4dd7-b366-99dfbd8c641b
-- title:
--   F256 Garcia Stichtenoth: intermediate Prime order nonnegative of ambient regular
-- statement:
--   Ambient regularity descends to the actual contracted integral-model
--   place, by the positive ramification scaling of its normalized order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinementRamification.lean#L36-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/RegularRefinementRamification.lean#L36-L56

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalRegular
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinementRamification
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

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.intermediatePrime_order_nonnegative_of_ambient_regular
    (K : IntermediateField F E) (a : K) (ha : (a : E) ∈ (R).valuationRing) :
    0 ≤ (heightOnePlace (k := F256) (K := K) (P K)).order a := by sorry
