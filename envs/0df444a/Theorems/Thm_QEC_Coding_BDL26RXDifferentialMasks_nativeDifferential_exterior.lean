-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_nativeDifferential_exterior
-- name    : QEC.Coding.BDL26RXDifferentialMasks.nativeDifferential_exterior
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:02:18.956208+00:00
-- url     : https://prove2.me/theorems/a7725e52-e327-4fa6-a460-a73b28e2e488
-- title:
--   BDL26 RXDifferential Masks: native Differential exterior
-- statement:
--   Every original unselected coordinate is zero for every input. This keeps
--   all genuine unparented connectors, rather than discarding them from the domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L266-L277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L266-L277

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.nativeDifferential_exterior (h : i.val % 2 = 0)
    (w : Word BDL26Field (state S i.val).presentation.Q)
    (p : FamilyZ S depth i.succ) (hp : p ∉ (rxData S depth i h).zSector) :
    nativeDifferential S depth i w p = 0 := by sorry
