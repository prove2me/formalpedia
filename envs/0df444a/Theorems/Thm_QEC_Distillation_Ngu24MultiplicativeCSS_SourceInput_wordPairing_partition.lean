-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_wordPairing_partition
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.wordPairing_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:45:42.180122+00:00
-- url     : https://prove2.me/theorems/c685d552-4a4d-48cd-ae51-779556c333d5
-- title:
--   Source Input: word Pairing partition
-- statement:
--   Every full pairing is the sum of its pivot and punctured contributions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L543-L590
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L543-L590

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.wordPairing_partition (data : SourceInput F I Logical)
    (left right : Word F I) :
    wordPairing left right =
      wordPairing (data.pivotCoordinates left) (data.pivotCoordinates right) +
        wordPairing (data.puncture left) (data.puncture right) := by sorry
