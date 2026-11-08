-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_baseCoboundary_squared
-- name    : QEC.Coding.BDL26FiniteAlternatingCore.baseCoboundary_squared
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:22:22.393114+00:00
-- url     : https://prove2.me/theorems/ecb0e02b-24ff-47e5-a84c-d2ddd98b94c9
-- title:
--   BDL26 Finite Alternating Core: base Coboundary squared
-- statement:
--   The concrete base coboundaries compose to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L279-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L279-L287

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

theorem QEC.Coding.BDL26FiniteAlternatingCore.baseCoboundary_squared :
    baseCoboundary1.comp baseCoboundary0 = 0 := by sorry
