-- Prove2me | Theorems.Thm_QEC_Distillation_mem_coordinateSupport
-- name    : QEC.Distillation.mem_coordinateSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:17:34.492952+00:00
-- url     : https://prove2.me/theorems/035f4be6-6fa8-433f-b4bb-71bcc0c3f0ee
-- title:
--   Distillation: mem coordinate Support
-- statement:
--   The Distillation construction uses the mem coordinate Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Register.lean#L94-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/Register.lean#L94-L97

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
universe u
variable {F ι : Type u} [Field F] [Fintype F]

theorem QEC.Distillation.mem_coordinateSupport [Fintype ι] [DecidableEq ι]
    {coordinate : TaggedThreeCopyCoordinate ι} {site : ι} :
    coordinate ∈ coordinateSupport site ↔ coordinate.2 = site := by sorry
