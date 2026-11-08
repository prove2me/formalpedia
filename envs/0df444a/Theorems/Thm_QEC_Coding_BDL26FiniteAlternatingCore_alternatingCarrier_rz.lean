-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_rz
-- name    : QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_rz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:22:48.312805+00:00
-- url     : https://prove2.me/theorems/be6bbc1a-5af4-4707-9e71-0d81d4fbfc36
-- title:
--   BDL26 Finite Alternating Core: alternating Carrier rz
-- statement:
--   RZ has the exact typed shape `C_(2i+1) -> C_(2i+2)` at carrier level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L369-L374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L369-L374

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

theorem QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_rz
    (seed : FiniteCochainCarrier) (S : AlternatingCarrierConstructors) (i : Nat) :
    alternatingCarrier seed S (2 * i + 2) =
      S.rz (rzStep i) (alternatingCarrier seed S (2 * i + 1)) := by sorry
