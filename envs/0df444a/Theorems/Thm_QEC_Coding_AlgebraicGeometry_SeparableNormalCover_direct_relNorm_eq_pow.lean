-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_SeparableNormalCover_direct_relNorm_eq_pow
-- name    : QEC.Coding.AlgebraicGeometry.SeparableNormalCover.direct_relNorm_eq_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:43:56.148343+00:00
-- url     : https://prove2.me/theorems/31637ba0-63db-40b1-bfdb-4922b441a2d8
-- title:
--   Separable Normal Cover: direct rel Norm eq pow
-- statement:
--   The direct prime relative-norm formula now follows from the constructed
--   finite integral Galois cover, without adding a separate structural premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/SeparableNormalCover.lean#L199-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/SeparableNormalCover.lean#L199-L204

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_SeparableNormalCover
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.SeparableNormalCover
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
local notation3 "R" => k[X]
local notation3 "B" => directRingOfIntegers k F
local notation3 "K" => FractionRing R
local notation3 "L" => FractionRing B
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_56
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_60
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_62
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_76
local notation3 "M" => SeparableClosure K
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_87
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_89
local notation3 "E" => IntermediateField.normalClosure K L M
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_96
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_98
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_100
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_102
local notation "T" => integralClosure B E
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_108
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_110
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_112
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_114
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_116
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_118
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_120
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_125
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_131
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_135
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_138
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_141
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_146
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_148
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_151
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_154
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_157
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_160
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_162
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_164
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_168
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_170
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_185
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover.directBFracAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_189
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_190
attribute [local instance] QEC.Coding.AlgebraicGeometry.SeparableNormalCover._p2m_local_instance_ece2c1af97_194

theorem QEC.Coding.AlgebraicGeometry.SeparableNormalCover.direct_relNorm_eq_pow
    (P : Ideal B) (p : Ideal R) [P.LiesOver p] [P.IsMaximal] [p.IsMaximal] :
    Ideal.relNorm R P = p ^ p.inertiaDeg' P := by sorry
