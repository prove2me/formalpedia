-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_nativeDifferential_basis
-- name    : QEC.Coding.BDL26RXDifferentialMasks.nativeDifferential_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:37:05.650744+00:00
-- url     : https://prove2.me/theorems/744c6a93-3eef-4512-aeaa-f8ec39f6e231
-- title:
--   BDL26 RXDifferential Masks: native Differential basis
-- statement:
--   The BDL26 RXDifferential Masks construction uses the native Differential basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L107-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L107-L108

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.nativeDifferential_basis (q : (state S i.val).presentation.Q) :
    nativeDifferential S depth i (canonicalBasisWord q) = basisImage S depth i q := by sorry

attribute [defeq] QEC.Coding.BDL26RXDifferentialMasks.nativeDifferential_basis
