-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OneLevelProtocolFamily_successfulOutputCost
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_successfulOutputCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:28:52.846601+00:00
-- url     : https://prove2.me/theorems/66e6b9bc-0dc6-4191-9a4e-e1cc7bc4d829
-- title:
--   BH12 Concatenation: bh12 One Level Protocol Family successful Output Cost
-- statement:
--   The #458 successful-output cost has the literal BH12 denominator: actual
--   logical-port count times actual raw success mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2141-L2149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2141-L2149

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_successfulOutputCost (q : Nat)
    (p : ErrorParameter) (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost port =
      (bh12InputCount q : ℝ) /
        ((bh12OutputCount q : ℝ) * rawSuccessMass q p) := by sorry
