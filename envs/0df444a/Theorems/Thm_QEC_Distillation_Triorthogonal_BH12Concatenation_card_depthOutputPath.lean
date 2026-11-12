-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_card_depthOutputPath
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.card_depthOutputPath
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:31:25.076279+00:00
-- url     : https://prove2.me/theorems/3e2dac96-c51f-4d56-ae50-d3f1e058028d
-- title:
--   BH12 Concatenation: card depth Output Path
-- statement:
--   The BH12 Concatenation construction uses the card depth Output Path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1488-L1490
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1488-L1490

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.card_depthOutputPath (q z : Nat) :
    Fintype.card (depthOutputPath q z) = (bh12OutputCount q) ^ z := by sorry
