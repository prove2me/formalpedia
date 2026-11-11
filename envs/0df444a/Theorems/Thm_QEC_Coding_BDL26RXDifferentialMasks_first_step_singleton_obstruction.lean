-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_first_step_singleton_obstruction
-- name    : QEC.Coding.BDL26RXDifferentialMasks.first_step_singleton_obstruction
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T22:34:06.865711+00:00
-- url     : https://prove2.me/theorems/5f848f63-462b-4baf-95a2-29c8b13a0338
-- title:
--   BDL26 RXDifferential Masks: first step singleton obstruction
-- statement:
--   A genuine finite seed witness at EVERY actual first RX step and every
--   original odd scale: Q0 and Q4 share Z0, so the singleton Q0 mask fails on e4.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L313-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L313-L326

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)
open BDL26FiniteAlternatingCore

theorem QEC.Coding.BDL26RXDifferentialMasks.first_step_singleton_obstruction (S : OddScale) (depth : Nat) (hd : 0 < depth) :
    maskWord (nativeRegion S depth ⟨0,hd⟩ (by rfl) {(0 : BaseQubit)})
        (nativeDifferential S depth ⟨0,hd⟩ (canonicalBasisWord (4 : BaseQubit))) ≠
      nativeDifferential S depth ⟨0,hd⟩
        (maskWord {(0 : BaseQubit)} (canonicalBasisWord (4 : BaseQubit))) := by sorry
