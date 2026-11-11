-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_nativeRegion_commutes_iff_saturated
-- name    : QEC.Coding.BDL26RXDifferentialMasks.nativeRegion_commutes_iff_saturated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:55:53.156733+00:00
-- url     : https://prove2.me/theorems/49b81925-d198-4839-83b7-51e5be71e953
-- title:
--   BDL26 RXDifferential Masks: native Region commutes iff saturated
-- statement:
--   This is the exact additional closure required by a forward incident-Z mask.
--   It cannot be omitted even if a particular input has syndrome cancellation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L161-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L161-L176

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.nativeRegion_commutes_iff_saturated (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q) :
    (∀ w, maskWord (nativeRegion S depth i h A) (nativeDifferential S depth i w) =
      nativeDifferential S depth i (maskWord A w)) ↔ IncidenceSaturated S depth i A := by sorry
