-- Prove2me | Theorems.Thm_QEC_Coding_f256SelectorFunctional_apply
-- name    : QEC.Coding.f256SelectorFunctional_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:11:08.227192+00:00
-- url     : https://prove2.me/theorems/8f1b1b3b-10c7-4b59-923a-fa7bbf4ad831
-- title:
--   Coding: f256 Selector Functional apply
-- statement:
--   Evaluation of the composed binary functional.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/Selector.lean#L22-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteFieldMultiplication/Selector.lean#L22-L23

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_MultiplicationEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_ReverseEmbedding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
set_option autoImplicit false
open QEC QEC.Coding

theorem QEC.Coding.f256SelectorFunctional_apply (v : Fin 512 → ZMod 2) :
    f256SelectorFunctional v = f256RMFEpsi (f256MFEPsi v) := by sorry
