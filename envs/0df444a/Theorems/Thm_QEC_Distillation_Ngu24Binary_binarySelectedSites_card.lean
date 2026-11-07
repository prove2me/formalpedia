-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binarySelectedSites_card
-- name    : QEC.Distillation.Ngu24Binary.binarySelectedSites_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:47:23.294713+00:00
-- url     : https://prove2.me/theorems/43fda9ce-e872-4944-9678-8376b94de203
-- title:
--   Ngu24 Binary: binary Selected Sites card
-- statement:
--   The Ngu24 Binary construction uses the binary Selected Sites card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L81-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTriples.lean#L81-L83

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTriples
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding
open scoped BigOperators
universe u
variable (J : Type u)
variable [Fintype J]

theorem QEC.Distillation.Ngu24Binary.binarySelectedSites_card :
    (binarySelectedSites J).card = Fintype.card J * f256SelectedCoordinates.card := by sorry
