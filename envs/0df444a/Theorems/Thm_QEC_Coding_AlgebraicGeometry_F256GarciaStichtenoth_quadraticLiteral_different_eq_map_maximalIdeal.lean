-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_different_eq_map_maximalIdeal
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_different_eq_map_maximalIdeal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:54:58.112204+00:00
-- url     : https://prove2.me/theorems/7a8f842b-2c77-4c02-a096-84e6053af828
-- title:
--   F256 Garcia Stichtenoth: quadratic Literal different eq map maximal Ideal
-- statement:
--   At a normalized simple pole, the actual different is the extended
--   maximal ideal of the lower valuation ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticDifferent.lean#L25-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticDifferent.lean#L25-L57

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_IntegralClosureOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticLocalModels
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K L : Type*} [_root_.Field K] [_root_.Field L]
  [Algebra F256 K] [Algebra K L]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_different_eq_map_maximalIdeal
    (P : GlobalPlace F256 K)
    [Algebra P.valuationRing L] [IsScalarTower P.valuationRing K L]
    [IsDedekindDomain (integralClosure P.valuationRing L)]
    [Module.IsTorsionFree P.valuationRing (integralClosure P.valuationRing L)]
    (a : K) (ha : P.order a = -1)
    (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) :
    differentIdeal P.valuationRing (integralClosure P.valuationRing L) =
      Ideal.map (algebraMap P.valuationRing (integralClosure P.valuationRing L))
        (IsLocalRing.maximalIdeal P.valuationRing) := by sorry
