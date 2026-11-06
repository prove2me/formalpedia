-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_localDerivativeLatticeGeneratorOrder_support_finite
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.localDerivativeLatticeGeneratorOrder_support_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:26:20.66388+00:00
-- url     : https://prove2.me/theorems/4d0a5249-9b1c-41ec-adea-fc93bf9e3736
-- title:
--   Function Field Differential: local Derivative Lattice Generator Order support finite
-- statement:
--   The intrinsic local derivative-lattice generator order has finite support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L949-L964
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L949-L964

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.localDerivativeLatticeGeneratorOrder_support_finite :
    (Function.support fun P : GlobalPlace k F =>
      localDerivativeLatticeGeneratorOrder (k := k) (F := F) P).Finite := by sorry
