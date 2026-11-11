-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_commuting_lower_saturated
-- name    : QEC.Coding.BDL26RXDifferentialMasks.commuting_lower_saturated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:00:36.757991+00:00
-- url     : https://prove2.me/theorems/ccc9247a-0f05-482f-b593-cbdf6b5c7c6c
-- title:
--   BDL26 RXDifferential Masks: commuting lower saturated
-- statement:
--   Every commuting lower/upper pair forces shared-Z saturation on its lower
--   mask, even if its upper mask additionally contains arbitrary exterior points.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L180-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L180-L187

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.commuting_lower_saturated (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q)
    (B : Finset (FamilyZ S depth i.succ))
    (hc : ∀ w, maskWord B (nativeDifferential S depth i w) =
      nativeDifferential S depth i (maskWord A w)) : IncidenceSaturated S depth i A := by sorry
