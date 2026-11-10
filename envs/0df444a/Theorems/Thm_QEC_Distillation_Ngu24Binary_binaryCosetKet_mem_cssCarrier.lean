-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryCosetKet_mem_cssCarrier
-- name    : QEC.Distillation.Ngu24Binary.binaryCosetKet_mem_cssCarrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:50:27.630026+00:00
-- url     : https://prove2.me/theorems/580b9acb-2b2b-45bc-a863-ecfbf3a4436f
-- title:
--   Ngu24 Binary: binary Coset Ket mem css Carrier
-- statement:
--   The Ngu24 Binary construction uses the binary Coset Ket mem css Carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L195-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryCSS.lean#L195-L205

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCSS
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
attribute [local instance] QEC.Distillation.Ngu24Binary.binaryCSSFieldWordFintype

theorem QEC.Distillation.Ngu24Binary.binaryCosetKet_mem_cssCarrier (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryCosetKet i u ∈ (binaryCSSCode i).stabilizer.code.carrier := by sorry
