-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12PhysicalFlaggedBatch_total_weight
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PhysicalFlaggedBatch_total_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:37:44.409452+00:00
-- url     : https://prove2.me/theorems/ccd08f34-2a59-49e8-a510-9ab7c109f0fe
-- title:
--   BH12 Concatenation: bh12 Physical Flagged Batch total weight
-- statement:
--   The physical-error weights normalize over the finite BH12 error space.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1968-L1970
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1968-L1970

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12PhysicalFlaggedBatch_total_weight (q : Nat) (p : ErrorParameter) :
    ∑ error : PhysicalError q, (bh12PhysicalFlaggedBatch q p).weight error = 1 := by sorry
