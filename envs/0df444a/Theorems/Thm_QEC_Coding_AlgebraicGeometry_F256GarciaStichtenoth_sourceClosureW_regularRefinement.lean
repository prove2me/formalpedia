-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceClosureW_regularRefinement
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_regularRefinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:46:01.381915+00:00
-- url     : https://prove2.me/theorems/af88a1df-79c3-4ac1-89a9-ca246228be0f
-- title:
--   F256 Garcia Stichtenoth: source Closure W regular Refinement
-- statement:
--   The complete closure admits a regular refinement at every place where
--   the actual w is a unit. Only this local condition is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureRegularRefinement.lean#L58-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/ClosureRegularRefinement.lean#L58-L95

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularSourceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureConjugateChains
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ClosureRegularRefinement
set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
attribute [local instance] sourceConstantBaseTower

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceClosureW_regularRefinement (m : ℕ)
    (Q : GlobalPlace F256 (SourceGaloisClosureField m))
    (hw : Q.valuation (sourceGaloisWClosureGenerator m : SourceGaloisClosureField m) = 1) :
    RegularRefinement Q (⊥ : IntermediateField (sourceClosureWBase m) (SourceGaloisClosureField m)) ⊤ := by sorry
