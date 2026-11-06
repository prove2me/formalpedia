-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finiteDimensional_riemannRochSubmodule
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.finiteDimensional_riemannRochSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:23:10.15601+00:00
-- url     : https://prove2.me/theorems/4088ec6f-56b9-4fa9-a590-3773af9d762a
-- title:
--   Global Place: finite Dimensional riemann Roch Submodule
-- statement:
--   The actual all-place valuation-bound Riemann--Roch submodule is finite
--   dimensional over the finite constant field.  The direct and inverse lattice
--   containments are constructed from `G`; no global dimension result is an input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/FiniteDimensional.lean#L120-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/FiniteDimensional.lean#L120-L157

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ChartContainment
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_FiniteDimensional
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc nonZeroDivisors
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.finiteDimensional_riemannRochSubmodule
    : letI : Algebra k F := @AffinePlace.constantAlgebra k F _ _ π
    ∀ G : Divisor (GlobalPlace k F),
      FiniteDimensional k (GlobalPlace.riemannRochSubmodule G) := by sorry
