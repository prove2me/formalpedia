-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureConjugateW_regularRefinement
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_regularRefinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:45:57.881995+00:00
-- url     : https://prove2.me/theorems/c66f7590-5944-40c2-bd75-70d0a822983b
-- title:
--   F256 Garcia Stichtenoth: source Closure Conjugate W regular Refinement
-- statement:
--   The full actual source conjugate has a regular w-rooted chain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureRegularRefinement.lean#L40-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureRegularRefinement.lean#L40-L54

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularSourceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularRefinement
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] sourceConstantBaseTower

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureConjugateW_regularRefinement (m : ℕ)
    (f : SourceField m →ₐ[GaloisBaseField] SourceGaloisClosureField m)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m))
    (hw : Q.valuation (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 1) :
    RegularRefinement Q (sourceClosureWBase m) (f.restrictScalars F256).fieldRange := by sorry
