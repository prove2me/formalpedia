-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_quadraticLiteral_heightOnePrime_weakDifferent
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_heightOnePrime_weakDifferent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:58:08.838597+00:00
-- url     : https://prove2.me/theorems/2f728ecc-08e9-4dfd-9c51-e4a7d7da410b
-- title:
--   F256 Garcia Stichtenoth: quadratic Literal height One Prime weak Different
-- statement:
--   The same global weak formula with the lower place constructed from the
--   supplied contracted prime. No independent place, valuation-ring equality, or
--   local different hypothesis is required.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticGlobalDifferent.lean#L66-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/QuadraticGlobalDifferent.lean#L66-L96

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_PlaceLocalization
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticGlobalDifferent
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.quadraticLiteral_heightOnePrime_weakDifferent
    (A B K L : Type*) [CommRing A] [CommRing B]
    [_root_.Field K] [_root_.Field L]
    [IsDomain A] [IsLocalRing A] [IsDedekindDomain B]
    [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]
    [Algebra F256 K] [Algebra F256 L]
    [Algebra B K] [IsFractionRing B K]
    [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Module.IsTorsionFree B L]
    [IsDedekindDomain (integralClosure B L)]
    [Module.IsTorsionFree B (integralClosure B L)]
    (H : IsDedekindDomain.HeightOneSpectrum B)
    (J : Ideal (integralClosure B L)) [J.IsPrime] [J.LiesOver H.asIdeal]
    (a : K) (y : L) (hy : y ^ 2 + y = algebraMap K L a)
    (hdegree : Module.finrank K L = 2) (hgen : K⟮y⟯ = ⊤)
    (ha : (heightOnePlace (k := F256) (K := K) H).order a = -1 ∨
      0 ≤ (heightOnePlace (k := F256) (K := K) H).order a) :
    multiplicity J (differentIdeal B (integralClosure B L)) =
      2 * (H.asIdeal.ramificationIdx' J - 1) := by sorry
