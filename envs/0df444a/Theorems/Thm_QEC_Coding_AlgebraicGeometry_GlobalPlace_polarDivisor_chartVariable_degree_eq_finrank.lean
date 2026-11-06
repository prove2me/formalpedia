-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_chartVariable_degree_eq_finrank
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_chartVariable_degree_eq_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:02:20.203577+00:00
-- url     : https://prove2.me/theorems/62af7ed4-7d7c-428c-b0f6-a150d370be97
-- title:
--   Global Place: polar Divisor chart Variable degree eq finrank
-- statement:
--   The pole divisor of the chosen rational coordinate has degree exactly the
--   rational-function extension degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PolarDegree.lean#L251-L266
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PolarDegree.lean#L251-L266

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_InverseFibrePrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarFamily
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators Polynomial RatFunc WithZero
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.riemannRochPolarDegreeAlgebra
attribute [local instance] riemannRochPolarDegreeAlgebra
open QEC.Coding.AlgebraicGeometry.GlobalPlace

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_chartVariable_degree_eq_finrank :
    Divisor.degree (residueDegree (k := k) (F := F))
        (polarDivisor (k := k) (F := F)
          (chartVariable (k := k) (F := F))) =
      (Module.finrank (RatFunc k) F : ℤ) := by sorry
