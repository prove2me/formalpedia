-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_RZ_constructor_card
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.RZ_constructor_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:21:35.865593+00:00
-- url     : https://prove2.me/theorems/36d39ae4-0848-4e3f-bea5-fa6d60bb2edd
-- title:
--   BDL26 Localized History Error Descent: RZ constructor card
-- statement:
--   All three actual constructors retain the exact 0/1/incidence-card table.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L700-L712
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L700-L712

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZPhysicalXStarTransport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalizedHistoryErrorDescent
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalizedHistoryErrorDescent
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat) (sigma tau : TopInput S n)
variable (top : LocalizedWord S n sigma tau (TopIndex n))

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.RZ_constructor_card (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (v : BDL26RZLocalReplacement.RZX (state S (Edge n i).val).presentation S) :
    (BDL26RZPhysicalXStarTransport.Q0 S (n+2) (Edge n i) h
      (BDL26RZPhysicalXStarTransport.upperXChart S (n+2) (Edge n i) h v)).card=
      match v with
      | .inl (.inl _) => 0
      | .inl (.inr _) => 1
      | .inr (x,_) => (BDL26RXPhysicalStarTransport.physicalXStar
          (state S (Edge n i).val).presentation x).card := by sorry
