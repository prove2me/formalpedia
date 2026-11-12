-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OneLevelProtocolFamily_outputResourceCount_eq_card_oddRow
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_outputResourceCount_eq_card_oddRow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:41:08.050111+00:00
-- url     : https://prove2.me/theorems/aacfde23-b2ff-413a-8403-92b48019a6ca
-- title:
--   BH12 Concatenation: bh12 One Level Protocol Family output Resource Count eq card odd Row
-- statement:
--   The reported family output count is the cardinality of the actual logical
--   register's BH12 port index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2114-L2119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2114-L2119

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_outputResourceCount_eq_card_oddRow
    (q : Nat) (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).outputResourceCount port =
      Fintype.card (OddRow q) := by sorry
