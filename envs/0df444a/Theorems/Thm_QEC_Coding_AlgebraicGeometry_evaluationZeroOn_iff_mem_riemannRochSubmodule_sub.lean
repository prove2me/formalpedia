-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_evaluationZeroOn_iff_mem_riemannRochSubmodule_sub
-- name    : QEC.Coding.AlgebraicGeometry.evaluationZeroOn_iff_mem_riemannRochSubmodule_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:07:19.647865+00:00
-- url     : https://prove2.me/theorems/57c26d39-bc40-4ba8-8cbc-160aa8fb55ce
-- title:
--   Algebraic Geometry: evaluation Zero On iff mem riemann Roch Submodule sub
-- statement:
--   The Algebraic Geometry construction uses the evaluation Zero On iff mem riemann Roch Submodule sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/EvaluationKernel.lean#L50-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/EvaluationKernel.lean#L50-L58

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Evaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationKernel
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
noncomputable section
variable {k F ι : Type*} [Field k] [Finite k] [Field F] [Algebra k F] [Fintype ι]

theorem QEC.Coding.AlgebraicGeometry.evaluationZeroOn_iff_mem_riemannRochSubmodule_sub
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (S : Finset ι)
    (f : GlobalPlace.riemannRochSubmodule G) :
    (∀ j ∈ S, agEvaluationLinearMap G Q hG f j = 0) ↔
      (f : F) ∈ GlobalPlace.riemannRochSubmodule (G - zeroCoordinateDivisor Q S) := by sorry
