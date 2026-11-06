-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureConjugateW_valuation_eq_one
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_valuation_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:45:08.345985+00:00
-- url     : https://prove2.me/theorems/7f04ba88-06be-45fa-806c-8a2641e7c535
-- title:
--   F256 Garcia Stichtenoth: source Closure Conjugate W valuation eq one
-- statement:
--   Every actual conjugate w-parameter is a unit wherever the chosen w is:
--   both fifteenth powers are the same embedded z.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureRegularRefinement.lean#L23-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureRegularRefinement.lean#L23-L37

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularSourceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularRefinement
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] sourceConstantBaseTower

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_valuation_eq_one (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m))
    (hw : Q.valuation (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 1) :
    Q.valuation (f (algebraMap (RatFunc F256) (SourceField m) galoisBaseW)) = 1 := by sorry
