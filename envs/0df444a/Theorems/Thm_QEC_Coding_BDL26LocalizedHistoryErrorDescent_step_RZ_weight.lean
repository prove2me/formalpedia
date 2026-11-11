-- Prove2me | Theorems.Thm_QEC_Coding_BDL26LocalizedHistoryErrorDescent_step_RZ_weight
-- name    : QEC.Coding.BDL26LocalizedHistoryErrorDescent.step_RZ_weight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T18:22:14.618389+00:00
-- url     : https://prove2.me/theorems/d1a9b795-841a-4973-9a79-e72451e0dc8d
-- title:
--   BDL26 Localized History Error Descent: step RZ weight
-- statement:
--   Sharp RZ input-block bound: the constructor cases compute 0,1,or an
--   old physical incidence star, never a bound on the full corrected upper word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L680-L688
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/LocalizedHistoryErrorDescent.lean#L680-L688

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

theorem QEC.Coding.BDL26LocalizedHistoryErrorDescent.step_RZ_weight (i : StepIndex n) (h : ¬(Edge n i).val%2=0)
    (u : LocalizedWord S n sigma tau i.succ) :
    HammingWeight (step S n sigma tau i u).lower.word ≤
        (BDL26RZPhysicalXStarTransport.Q0 S (n+2) (Edge n i) h u.center).card ∧
      (BDL26RZPhysicalXStarTransport.Q0 S (n+2) (Edge n i) h u.center).card≤7 := by sorry
