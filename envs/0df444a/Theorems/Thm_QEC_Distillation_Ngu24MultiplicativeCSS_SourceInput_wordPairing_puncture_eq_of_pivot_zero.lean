-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_wordPairing_puncture_eq_of_pivot_zero
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.wordPairing_puncture_eq_of_pivot_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:10:34.837567+00:00
-- url     : https://prove2.me/theorems/ab8175e5-2095-4726-be6c-774dc7ebfd2d
-- title:
--   Source Input: word Pairing puncture eq of pivot zero
-- statement:
--   Puncturing preserves pairing when the left word vanishes on all pivots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L167-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L167-L213

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_CSSShortening
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24MultiplicativeCSS
open Coding Semantics
open scoped BigOperators
universe u
variable {F I Logical : Type u} [Field F] [Fintype F] [Fintype I] [Fintype Logical]
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_23
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_24
attribute [local instance] QEC.Distillation.Ngu24MultiplicativeCSS._p2m_local_instance_7d0f4269de_25
open QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.wordPairing_puncture_eq_of_pivot_zero (data : SourceInput F I Logical)
    (left right : Word F I) (hzero : data.pivotCoordinates left = 0) :
    wordPairing (data.puncture left) (data.puncture right) = wordPairing left right := by sorry
