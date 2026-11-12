-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_nativeDifferential_connector
-- name    : QEC.Coding.BDL26RXDifferentialMasks.nativeDifferential_connector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T22:30:49.126269+00:00
-- url     : https://prove2.me/theorems/ee807eff-fec6-4466-832d-eaf3a4a3d32e
-- title:
--   BDL26 RXDifferential Masks: native Differential connector
-- statement:
--   The BDL26 RXDifferential Masks construction uses the native Differential connector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L279-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXDifferentialMasks.lean#L279-L285

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXQConcreteCoherence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXDifferentialMasks
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDifferentialMasks
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26RXDecoderAdapter BDL26RXQConcreteCoherence
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth)

theorem QEC.Coding.BDL26RXDifferentialMasks.nativeDifferential_connector (h : i.val % 2 = 0)
    (q : (state S i.val).presentation.Q)
    (w : Word BDL26Field (state S i.val).presentation.Q) :
    parent S (i.val+1) (Vertex.z (connector S depth i h q)) = none ∧
      nativeDifferential S depth i w (connector S depth i h q) = 0 := by sorry
