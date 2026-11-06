-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_globalSimplePoleResidueSum_riemannRochProductDifferential_eq_selected
-- name    : QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_riemannRochProductDifferential_eq_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:40:45.813643+00:00
-- url     : https://prove2.me/theorems/2ddc12e2-1eaf-4196-909d-5d03a584c68f
-- title:
--   Differential: global Simple Pole Residue Sum riemann Roch Product Differential eq selected
-- statement:
--   The finite residue sum of a one-place product differential is its
--   selected-place coefficient.  This is a support identity only; no vanishing
--   of that coefficient is asserted.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ResidueSupportSum.lean#L38-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/ResidueSupportSum.lean#L38-L60

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ResidueProduct
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_ResidueSupportSum
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (Polynomial k) F] [Algebra (RatFunc k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]
variable [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.Differential.globalSimplePoleResidueSum_riemannRochProductDifferential_eq_selected
    (omega : Differential k F) (homega : omega ≠ 0)
    (G : Divisor (GlobalPlace k F)) (P : GlobalPlace k F)
    (x : GlobalPlace.riemannRochSubmodule (G + P.placeDivisor))
    (y : GlobalPlace.riemannRochSubmodule
      (differentialDivisor (k := k) (F := F) omega homega - G)) :
    globalSimplePoleResidueSum (k := k) (F := F)
        (riemannRochProductDifferential omega homega G P x y)
        (riemannRochProductDifferential_isGlobalSimplePole
          omega homega G P x y) =
      globalSimplePoleResidue (k := k) (F := F)
        (riemannRochProductDifferential omega homega G P x y)
        (riemannRochProductDifferential_isGlobalSimplePole
          omega homega G P x y) P := by sorry
