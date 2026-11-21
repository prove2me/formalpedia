-- Prove2me | Theorems.Thm_QEC_Distillation_bk05TCompleteSemanticSchedule_rootOutput_eq_diagonalInput
-- name    : QEC.Distillation.bk05TCompleteSemanticSchedule_rootOutput_eq_diagonalInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T21:56:04.034183+00:00
-- url     : https://prove2.me/theorems/c6e15736-769e-40a0-9700-ee53a0c75ce2
-- title:
--   Distillation: bk05 TComplete Semantic Schedule root Output eq diagonal Input
-- statement:
--   The Distillation construction uses the bk05 TComplete Semantic Schedule root Output eq diagonal Input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L108-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MagicStateThreshold/Universality.lean#L108-L125

import Definitions.Def_QEC_Distillation_MagicStateThreshold_Universality
set_option autoImplicit false
noncomputable section
universe u v
open QEC
open QEC.Distillation
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open OneQubitMagic
open GeneratedUniversality
open FiniteRegisterUniversality
open FiniteRegisterUniversality.FiniteRegisterCircuit
open scoped BigOperators Matrix.Norms.Elementwise

theorem QEC.Distillation.bk05TCompleteSemanticSchedule_rootOutput_eq_diagonalInput
    (rho : DensityOperator QubitSpace)
    (hthreshold : tInitialError rho < BK05T.bk05TThreshold) (rounds : Nat) :
    BK05TSemanticSchedule.rootOutput
        (bk05TCompleteSemanticSchedule rho hthreshold rounds) =
      BK05T.tDiagonalInput (tIteration rho rounds)
        (tIteration_bounds rho hthreshold rounds).1
        (tIteration_le_one rho hthreshold rounds) := by sorry
