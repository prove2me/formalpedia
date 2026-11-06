-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepFieldEquiv_stepFieldEmbedding
-- name    : QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepFieldEmbedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:51:07.21926+00:00
-- url     : https://prove2.me/theorems/c5fbdfa6-4282-4569-b324-eb3e76e69265
-- title:
--   F256 Garcia Stichtenoth: step Field Equiv step Field Embedding
-- statement:
--   The F256 Garcia Stichtenoth construction uses the step Field Equiv step Field Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/StepTransport.lean#L49-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/StepTransport.lean#L49-L56

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Step
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepTransport
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]

theorem QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepFieldEquiv_stepFieldEmbedding
    (P Q : GlobalPlace F256 K) (x : K)
    (hP : P.order x = -1) (hQ : Q.order x = -1) (y : K) :
    stepFieldEquiv P Q x hP hQ (stepFieldEmbedding P x hP y) =
      stepFieldEmbedding Q x hQ y := by sorry
