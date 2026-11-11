-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_blochProjector_injective
-- name    : QEC.Distillation.OneQubitMagic.blochProjector_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:02:02.883416+00:00
-- url     : https://prove2.me/theorems/3e35c159-3a90-4cb7-bf8b-73de79f5c106
-- title:
--   One Qubit Magic: bloch Projector injective
-- statement:
--   The One Qubit Magic construction uses the bloch Projector injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L181-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/OneQubitMagicState.lean#L181-L187

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_Universality_OneQubitMagicState
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit

theorem QEC.Distillation.OneQubitMagic.blochProjector_injective : Function.Injective blochProjector := by sorry
