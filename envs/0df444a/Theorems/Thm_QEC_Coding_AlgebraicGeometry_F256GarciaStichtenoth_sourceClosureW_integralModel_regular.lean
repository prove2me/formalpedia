-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureW_integralModel_regular
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_integralModel_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:17:20.276298+00:00
-- url     : https://prove2.me/theorems/4a7cef61-872c-48a3-bb49-7f24f18d8348
-- title:
--   F256 Garcia Stichtenoth: source Closure W integral Model regular
-- statement:
--   Every prime at which the literal w is a unit has index one and
--   different exponent zero in the actual closure over k(w).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureUnramified.lean#L31-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureUnramified.lean#L31-L41

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureDifferent
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinementRamification
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisWPrincipalDivisor
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureUnramified
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] closureDifferent_modelDedekind closureDifferent_modelFinite
  closureDifferent_modelFraction closureDifferent_modelTorsionFree
variable (m : ℕ) (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (sourceClosureWBase m)] [IsFractionRing A (sourceClosureWBase m)]
    [Algebra A (SourceGaloisClosureField m)]
    [IsScalarTower A (sourceClosureWBase m) (SourceGaloisClosureField m)]
    [Module.IsTorsionFree A (SourceGaloisClosureField m)]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_integralModel_regular
    (Q : IsDedekindDomain.HeightOneSpectrum (integralClosure A (SourceGaloisClosureField m)))
    (hw : (heightOnePlace (k := F256) (K := SourceGaloisClosureField m) Q).valuation
      (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 1) :
    (Q.under A).asIdeal.ramificationIdx' Q.asIdeal = 1 ∧
      multiplicity Q.asIdeal (differentIdeal A (integralClosure A (SourceGaloisClosureField m))) = 0 := by sorry
