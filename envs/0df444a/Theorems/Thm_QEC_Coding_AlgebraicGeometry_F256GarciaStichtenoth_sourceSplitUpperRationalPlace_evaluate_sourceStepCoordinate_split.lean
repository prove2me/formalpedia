-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_split
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:36:32.134765+00:00
-- url     : https://prove2.me/theorems/c6d4fd76-0b03-40b6-b6a3-bb053ef979f2
-- title:
--   F256 Garcia Stichtenoth: source Split Upper Rational Place evaluate source Step Coordinate split
-- statement:
--   The evaluated successor coordinate again satisfies the exact nonzero
--   split condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitEvaluation.lean#L176-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitEvaluation.lean#L176-L189

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_evaluate_sourceStepCoordinate_split
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier) :
    galoisBaseWValue
        ((sourceSplitUpperRationalPlace Q P x hx hregular hsplit c).evaluateRegular
          (sourceStepCoordinate P x hx)
          (sourceSplitAbovePlace_sourceStepCoordinate_regular
            Q P x hx hregular hsplit c)) ≠ 0 := by sorry
