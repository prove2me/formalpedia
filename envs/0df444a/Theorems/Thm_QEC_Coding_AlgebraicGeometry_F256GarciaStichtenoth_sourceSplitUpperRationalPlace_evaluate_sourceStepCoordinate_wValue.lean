-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_wValue
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_wValue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:36:53.599177+00:00
-- url     : https://prove2.me/theorems/0b960490-8a20-40ea-bcc2-d5b85914e218
-- title:
--   F256 Garcia Stichtenoth: source Split Upper Rational Place evaluate source Step Coordinate w Value
-- statement:
--   Evaluating the successor equation identifies its Artin--Schreier value
--   with the literal source right-hand side at the parent residue value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitEvaluation.lean#L133-L172
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitEvaluation.lean#L133-L172

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_wValue
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    galoisBaseWValue
        ((sourceSplitUpperRationalPlace Q P x hx hregular hsplit c).evaluateRegular
          (sourceStepCoordinate P x hx)
          (sourceSplitAbovePlace_sourceStepCoordinate_regular
            Q P x hx hregular hsplit c)) =
      sourceStepRhs (Q.evaluateRegular x hregular) := by sorry
