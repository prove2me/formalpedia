-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteAlternatingCore_replacementKind_eq_rz_iff
-- name    : QEC.Coding.BDL26FiniteAlternatingCore.replacementKind_eq_rz_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:21:52.436937+00:00
-- url     : https://prove2.me/theorems/99461059-e9f8-4e19-b93e-d59616c716c5
-- title:
--   BDL26 Finite Alternating Core: replacement Kind eq rz iff
-- statement:
--   The parity selector names RZ exactly at odd source levels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L319-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/Core.lean#L319-L322

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

theorem QEC.Coding.BDL26FiniteAlternatingCore.replacementKind_eq_rz_iff (i : Nat) :
    replacementKind i = .rz ↔ i % 2 = 1 := by sorry
