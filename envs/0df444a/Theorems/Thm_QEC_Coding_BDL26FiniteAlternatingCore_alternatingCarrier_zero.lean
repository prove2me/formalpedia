-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_zero
-- name    : QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:12:29.474411+00:00
-- url     : https://prove2.me/theorems/e5667a51-868b-4b60-9856-47f2c67ebafe
-- title:
--   BDL26 Finite Alternating Core: alternating Carrier zero
-- statement:
--   The BDL26 Finite Alternating Core construction uses the alternating Carrier zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L356-L359
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L356-L359

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

theorem QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
    (seed : FiniteCochainCarrier) (S : AlternatingCarrierConstructors) :
    alternatingCarrier seed S 0 = seed := by sorry

attribute [defeq] QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_zero
