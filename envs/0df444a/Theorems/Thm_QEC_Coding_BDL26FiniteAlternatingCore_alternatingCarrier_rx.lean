-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_alternatingCarrier_rx
-- name    : QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_rx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:22:08.585054+00:00
-- url     : https://prove2.me/theorems/41e8f57f-844f-4be3-8b31-7c1007140631
-- title:
--   BDL26 Finite Alternating Core: alternating Carrier rx
-- statement:
--   RX has the exact typed shape `C_(2i) -> C_(2i+1)` at carrier level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L362-L366
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L362-L366

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

theorem QEC.Coding.BDL26FiniteAlternatingCore.alternatingCarrier_rx
    (seed : FiniteCochainCarrier) (S : AlternatingCarrierConstructors) (i : Nat) :
    alternatingCarrier seed S (2 * i + 1) =
      S.rx (rxStep i) (alternatingCarrier seed S (2 * i)) := by sorry
