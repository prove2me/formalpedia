-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_normalizedEvaluationCanonicalDivisor_isCanonical
-- name    : QEC.Coding.AlgebraicGeometry.normalizedEvaluationCanonicalDivisor_isCanonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:16:32.895741+00:00
-- url     : https://prove2.me/theorems/7001119e-a6b8-4a8e-8918-eb8b32a0aca1
-- title:
--   Algebraic Geometry: normalized Evaluation Canonical Divisor is Canonical
-- statement:
--   The normalized evaluation divisor is an actual canonical divisor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/CodeDuality.lean#L1139-L1150
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/CodeDuality.lean#L1139-L1150

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Theorem
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_CodeDuality
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithTop WithZero
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.agCodeDualityAlgebra
attribute [local instance] agCodeDualityAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.agCodeDualityScalarTower
attribute [local instance] agCodeDualityScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.agCodeDualityFiniteDimensional
attribute [local instance] agCodeDualityFiniteDimensional
variable [IsFullConstantField k F]
variable {ι : Type*} [Fintype ι]
variable [Nonempty ι]

theorem QEC.Coding.AlgebraicGeometry.normalizedEvaluationCanonicalDivisor_isCanonical
    (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun i => (Q i).place) :
    FunctionFieldDifferential.IsCanonicalDivisor (k := k) (F := F)
      (normalizedEvaluationCanonicalDivisor
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F Q hQ) := by sorry
