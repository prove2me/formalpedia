-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_represented_RZ_records
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.represented_RZ_records
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T18:20:52.496028+00:00
-- url     : https://prove2.me/theorems/104ca469-d25d-48a0-9112-9497c5208b0b
-- title:
--   BDL26 Localized History Error Descent: represented RZ records
-- statement:
--   Both complete represented RZ records are the original snapshots.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L648-L655
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L648-L655

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.represented_RZ_records (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    BDL26RZErrorPullback.run S (n+2) (Edge n i) h (first S n sigma i)=
        BDL26CanonicalHistoryMarks.outputAt S n sigma i ∧
      BDL26RZErrorPullback.run S (n+2) (Edge n i) h (second S n sigma tau i u)=
        BDL26CanonicalHistoryMarks.outputAt S n tau i := by sorry
