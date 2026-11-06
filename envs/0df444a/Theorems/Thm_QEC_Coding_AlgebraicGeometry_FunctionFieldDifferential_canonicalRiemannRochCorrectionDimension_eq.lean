-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_canonicalRiemannRochCorrectionDimension_eq
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.canonicalRiemannRochCorrectionDimension_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:29:03.062223+00:00
-- url     : https://prove2.me/theorems/313e80ea-37c9-4ac1-b707-adede5852415
-- title:
--   Function Field Differential: canonical Riemann Roch Correction Dimension eq
-- statement:
--   The finite-dimensional correction term `ℓ(K - G)` is independent of the
--   actual canonical divisor representative `K`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/CanonicalCorrection.lean#L36-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/CanonicalCorrection.lean#L36-L60

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_CanonicalCorrection
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
variable [Algebra (Polynomial k) F]
variable [IsScalarTower (Polynomial k) (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.canonicalRiemannRochCorrectionDimension_eq
    {K L : Divisor (GlobalPlace k F)}
    (hK : IsCanonicalDivisor (k := k) (F := F) K)
    (hL : IsCanonicalDivisor (k := k) (F := F) L)
    (G : Divisor (GlobalPlace k F))
    [FiniteDimensional k (GlobalPlace.riemannRochSubmodule (K - G))]
    [FiniteDimensional k (GlobalPlace.riemannRochSubmodule (L - G))] :
    GlobalPlace.riemannRochDimension (K - G) =
      GlobalPlace.riemannRochDimension (L - G) := by sorry
