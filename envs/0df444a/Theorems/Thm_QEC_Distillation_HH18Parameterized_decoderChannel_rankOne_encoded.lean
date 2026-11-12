-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decoderChannel_rankOne_encoded
-- name    : QEC.Distillation.HH18Parameterized.decoderChannel_rankOne_encoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:01:10.865278+00:00
-- url     : https://prove2.me/theorems/50eacd25-5f40-4247-b828-9c8e12d2240d
-- title:
--   HH18 Parameterized: decoder Channel rank One encoded
-- statement:
--   The total decoder agrees with coherent inverse encoding on every encoded
--   rank-one input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Decoder.lean#L242-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Decoder.lean#L242-L267

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Types
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Decoder
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.HH18Parameterized.decoderChannel_rankOne_encoded {w r m : Nat} (h : Admissible w r m)
    (psi : LogicalRegister m w) :
    decoderChannel h (InnerProductSpace.rankOne Complex
      (ambientEncodingIsometry h psi) (ambientEncodingIsometry h psi)).toLinearMap =
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap := by sorry
