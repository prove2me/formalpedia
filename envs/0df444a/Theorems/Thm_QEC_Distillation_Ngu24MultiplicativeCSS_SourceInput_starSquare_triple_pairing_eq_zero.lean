-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24MultiplicativeCSS_SourceInput_starSquare_triple_pairing_eq_zero
-- name    : QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.starSquare_triple_pairing_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:46:15.17695+00:00
-- url     : https://prove2.me/theorems/f41b092a-7f3c-4964-8d5a-741f16b1258f
-- title:
--   Source Input: star Square triple pairing eq zero
-- statement:
--   Star-square containment gives the source's full-word triple-pairing consequence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L693-L699
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/CSSShortening.lean#L693-L699

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

theorem QEC.Distillation.Ngu24MultiplicativeCSS.SourceInput.starSquare_triple_pairing_eq_zero (data : SourceInput F I Logical)
    {x y z : Word F I} (hx : x ∈ data.code.carrier) (hy : y ∈ data.code.carrier)
    (hz : z ∈ data.code.carrier) :
    wordPairing (wordStar x y) z = 0 := by sorry
