-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_native_mask
-- name    : QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_native_mask
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:31:01.261854+00:00
-- url     : https://prove2.me/theorems/118438c9-e74c-46a1-b462-b9a390c94008
-- title:
--   BDL26 RXDifferential Masks: incidence Hull native mask
-- statement:
--   A constructed, non-oracular all-input native mask theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L236-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L236-L243

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.incidenceHull_native_mask (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q)
    (w : Word BDL26Field (state S i.val).presentation.Q) :
    maskWord (nativeRegion S depth i h (incidenceHull S depth i A))
        (nativeDifferential S depth i w) =
      nativeDifferential S depth i (maskWord (incidenceHull S depth i A) w) := by sorry
