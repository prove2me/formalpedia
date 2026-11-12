-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OneLevelProtocolFamily_successProbability
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_successProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:25:55.984336+00:00
-- url     : https://prove2.me/theorems/a97c21dd-284e-407f-8102-ef277405dd75
-- title:
--   BH12 Concatenation: bh12 One Level Protocol Family success Probability
-- statement:
--   The family retains the actual finite BH12 raw success mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2122-L2127
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2122-L2127

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_successProbability (q : Nat)
    (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    ((bh12OneLevelProtocolFamily q p hhalf).protocol port).run.successProbability =
      rawSuccessMass q p := by sorry
