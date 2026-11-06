-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_evaluate_sourceStepEmbedding
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_evaluate_sourceStepEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:36:26.624965+00:00
-- url     : https://prove2.me/theorems/c3e1df17-559c-44d1-bef2-7612ccc61074
-- title:
--   F256 Garcia Stichtenoth: source Split Upper Rational Place evaluate source Step Embedding
-- statement:
--   Evaluation of an embedded regular base function agrees with its original
--   rational-place evaluation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitEvaluation.lean#L57-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/SourceSplitEvaluation.lean#L57-L112

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_evaluate_sourceStepEmbedding
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier)
    (f : K) (hf : GlobalPlace.RegularAt Q.place f) :
    (sourceSplitUpperRationalPlace Q P x hx hregular hsplit c).evaluateRegular
        (sourceStepEmbedding P x hx f)
        (sourceSplitAbovePlace_sourceStepEmbedding_regular
          Q P x hx c f hf) =
      Q.evaluateRegular f hf := by sorry
