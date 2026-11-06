-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectNormCount_direct_sum_ramification_inertia
-- name    : QEC.Coding.AlgebraicGeometry.DirectNormCount.direct_sum_ramification_inertia
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:13:30.880923+00:00
-- url     : https://prove2.me/theorems/fdf4f4a2-553f-41a2-af7b-4c4158182924
-- title:
--   Direct Norm Count: direct sum ramification inertia
-- statement:
--   The direct integral closure has the genuine finite ramification/inertia
--   identity at every nonzero base prime.  Both the upper-place container and its
--   summands are constructed by Mathlib from the actual mapped ideal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectNormCount.lean#L71-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectNormCount.lean#L71-L81

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

theorem QEC.Coding.AlgebraicGeometry.DirectNormCount.direct_sum_ramification_inertia
    {p : Ideal k[X]} [p.IsMaximal] (hp : p ≠ ⊥) :
    ∑ P ∈ IsDedekindDomain.primesOverFinset p (directRingOfIntegers k F),
      p.ramificationIdx' P * p.inertiaDeg' P = Module.finrank k⟮X⟯ F := by sorry
