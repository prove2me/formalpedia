-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectNormCount_direct_intNorm_represents_fieldNorm
-- name    : QEC.Coding.AlgebraicGeometry.DirectNormCount.direct_intNorm_represents_fieldNorm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:17:16.984381+00:00
-- url     : https://prove2.me/theorems/4d88d5c0-5117-4447-b681-0b061661fcd7
-- title:
--   Direct Norm Count: direct int Norm represents field Norm
-- statement:
--   The integral norm in the preceding principal ideal represents the actual
--   field norm after the fraction-ring embedding.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectNormCount.lean#L42-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectNormCount.lean#L42-L51

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectNormCount
open scoped Polynomial RatFunc nonZeroDivisors
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectNormCount._p2m_local_instance_154c3067f1_22

theorem QEC.Coding.AlgebraicGeometry.DirectNormCount.direct_intNorm_represents_fieldNorm (x : directRingOfIntegers k F) :
    algebraMap k[X] k⟮X⟯ (Algebra.intNorm k[X] (directRingOfIntegers k F) x) =
      Algebra.norm k⟮X⟯ (algebraMap (directRingOfIntegers k F) F x) := by sorry
