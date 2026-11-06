-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidue_riemannRochProductDifferential_apply_eq_zero
-- name    : QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_riemannRochProductDifferential_apply_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:30:37.978353+00:00
-- url     : https://prove2.me/theorems/424bc011-697b-48ac-a711-0e706e57bfe5
-- title:
--   Differential: global Simple Pole Residue riemann Roch Product Differential apply eq zero
-- statement:
--   The selected traced residue of the actual one-place Riemann--Roch product
--   differential vanishes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ResiduePairing.lean#L47-L63
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ResiduePairing.lean#L47-L63

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ResidueSupportSum
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ResiduePairing
set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra (RatFunc k) F]
variable [IsScalarTower k[X] (RatFunc k) F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential._p2m_local_instance_93312dda23_36
attribute [local instance] QEC.Coding.AlgebraicGeometry.Differential._p2m_local_instance_93312dda23_38

theorem QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidue_riemannRochProductDifferential_apply_eq_zero
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    globalSimplePoleResidue (k := k) (F := F)
        (riemannRochProductDifferential omega homega G P x y)
        (riemannRochProductDifferential_isGlobalSimplePole
          omega homega G P x y) P = 0 := by sorry
