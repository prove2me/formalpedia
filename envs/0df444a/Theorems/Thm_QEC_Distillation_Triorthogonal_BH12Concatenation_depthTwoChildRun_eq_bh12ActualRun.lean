-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_depthTwoChildRun_eq_bh12ActualRun
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildRun_eq_bh12ActualRun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:27:23.274239+00:00
-- url     : https://prove2.me/theorems/3232bbf1-1f6e-48f6-840b-431fff89c440
-- title:
--   BH12 Concatenation: depth Two Child Run eq bh12 Actual Run
-- statement:
--   Once the parent success mass is positive, the child run is exactly the
--   ordinary BH12 run at the derived decoded-marginal parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1382-L1387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1382-L1387

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildRun_eq_bh12ActualRun (q : Nat) (p : ErrorParameter)
    (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    depthTwoChildRun q p port =
      bh12ActualRun q (bh12DecodedMarginalErrorParameter q p hsuccess port) := by sorry
