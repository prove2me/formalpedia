-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectNormCount_direct_inertia_eq_actual_residue_extension_degree
-- name    : QEC.Coding.AlgebraicGeometry.DirectNormCount.direct_inertia_eq_actual_residue_extension_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:13:35.810286+00:00
-- url     : https://prove2.me/theorems/94da072a-d686-4fe0-9142-bb2ee2f5caec
-- title:
--   Direct Norm Count: direct inertia eq actual residue extension degree
-- statement:
--   The Mathlib inertia degree is the degree of the actual residue-field
--   extension for the contracted direct base prime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectNormCount.lean#L55-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectNormCount.lean#L55-L66

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

theorem QEC.Coding.AlgebraicGeometry.DirectNormCount.direct_inertia_eq_actual_residue_extension_degree
    (P : AffinePlace.carrier k F) :
    (directBasePrime k F P).inertiaDeg' P.asIdeal =
      P.asIdeal.inertiaDeg k[X] := by sorry
