-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_native_mask_commutes_iff
-- name    : QEC.Coding.BDL26RXDifferentialMasks.native_mask_commutes_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:38:13.93295+00:00
-- url     : https://prove2.me/theorems/4b7f5ba0-39bc-41cc-9229-72dae9372d8c
-- title:
--   BDL26 RXDifferential Masks: native mask commutes iff
-- statement:
--   Exact all-input characterization at every actual legal RX step. Both real
--   Z copies occur, and no constraint is introduced on unselected connectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L112-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L112-L129

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.native_mask_commutes_iff (h : i.val % 2 = 0)
    (A : Finset (state S i.val).presentation.Q)
    (B : Finset (FamilyZ S depth i.succ)) :
    (∀ w, maskWord B (nativeDifferential S depth i w) =
      nativeDifferential S depth i (maskWord A w)) ↔
    ∀ q z (copy : Fin 2), (state S i.val).presentation.qz q z = true →
      (((rxData S depth i h).induced.zPairEquiv (z,copy)).val ∈ B ↔ q ∈ A) := by sorry
