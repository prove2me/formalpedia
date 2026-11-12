-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_card_depthRawInputPath
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.card_depthRawInputPath
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:30:52.76599+00:00
-- url     : https://prove2.me/theorems/8ab619d7-20e5-41d1-91ba-3692dc9691c7
-- title:
--   BH12 Concatenation: card depth Raw Input Path
-- statement:
--   The BH12 Concatenation construction uses the card depth Raw Input Path property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1484-L1486
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1484-L1486

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.card_depthRawInputPath (q z : Nat) :
    Fintype.card (depthRawInputPath q z) = (bh12InputCount q) ^ z := by sorry
