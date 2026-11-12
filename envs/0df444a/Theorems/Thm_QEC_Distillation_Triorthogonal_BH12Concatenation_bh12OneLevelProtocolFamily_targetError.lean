-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12OneLevelProtocolFamily_targetError
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_targetError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:39:48.086283+00:00
-- url     : https://prove2.me/theorems/a3e45f2e-b8ea-4e13-bfd1-3e29aaf58b83
-- title:
--   BH12 Concatenation: bh12 One Level Protocol Family target Error
-- statement:
--   The target is exactly the actual BH12 quadratic error bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2076-L2080
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L2076-L2080

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12OneLevelProtocolFamily_targetError (q : Nat) (p : ErrorParameter)
    (hhalf : p.rate ≤ 1 / 2) (port : OddRow q) :
    (bh12OneLevelProtocolFamily q p hhalf).targetError port =
      quadraticCoefficient q * p.rate ^ 2 := by sorry
