-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_finiteRx_target_val
-- name    : QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:11:57.825702+00:00
-- url     : https://prove2.me/theorems/113669ba-6783-4b09-9fca-026aa003d888
-- title:
--   BDL26 Finite Alternating Core: finite Rx target val
-- statement:
--   The BDL26 Finite Alternating Core construction uses the finite Rx target val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L389-L390
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L389-L390

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Mathlib.LinearAlgebra.StdBasis
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_Core
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26FiniteAlternatingCore
open MultiscaleDecoder
open Module
attribute [instance] FiniteCochainCarrier.fintypeC0
attribute [instance] FiniteCochainCarrier.fintypeC1
attribute [instance] FiniteCochainCarrier.fintypeC2

theorem QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val (depth i : Nat) (h : 2 * i < depth) :
    (finiteRxStepIndex depth i h).succ.val = 2 * i + 1 := by sorry

attribute [defeq] QEC.Coding.BDL26FiniteAlternatingCore.finiteRx_target_val
